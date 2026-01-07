import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Data.PNat.Notation
import Mathlib.Data.Nat.Prime.Defs
import Init.Data.Nat.Gcd
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Logic.Function.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
-- import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Algebra.Group.TypeTags.Basic

-- 1. Let S be a set. Prove that the law of composition defined by ab=a for all a and b in S is associative
def op {S : Type} (a : S) (b : S) : S := a

example {S : Type} (a b c : S) : op a (op b c) = op (op a b) c := by
  rfl


-- 2. If an element of a set (equipped with law of composition that is associative and has a identity) has both a left inverse l and a right inverse r,
-- i.e. if la = e (identity) and ar = 1, then l = r

-- simplified by realizing we are actually dealing with monoids
example {α : Type} [Monoid α] (a l r: α) (h₁ : l * a = 1) (h₂ : a * r = 1) : (l = r) := by
  calc
    l = l * 1 := by simp
    _= l * (a * r) := by rw [h₂]
    _= (l * a) * r := by rw [mul_assoc]
    _= 1 * r := by rw [h₁]
    _= r := by simp

-- 3, If an element of a set (equipped with law of composition that is associative and has a identity) is invertible, then the inverse is unique.

example {α : Type} [Monoid α] (a b c : α) (h₁ : a * c = 1) (h₂ : c * a = 1) (h₃ : a * b = 1) (h₄ : b * a = 1) : b = c := by
  calc
    b = b * 1 := by simp
    _= b * (a * c) := by rw [h₁]
    _= (b * a) * c := by rw [mul_assoc]
    _= 1 * c := by rw [h₄]
    _= c := by simp

-- 4. Given a set (equipped with law of composition that is associative and has a identity), if a and b are invertible, so is the product of ab.

example {α : Type} [Monoid α] (a b c d : α) (h₁ : a * c = 1) (h₂ : c * a = 1) (h₃ : b * d = 1) (h₄ : d * b =1) : ∃ (f : α), (f * (a * b) = 1) ∧ ((a * b) * f = 1) := by
  have l1 : (d * c) * (a * b) = 1 := by
    calc
      (d * c) * (a * b) = d * (c * a) * b := by rw [mul_assoc, mul_assoc, mul_assoc]
      _= d * 1 * b := by rw [h₂]
      _= d * b := by simp
      _= 1 := by rw [h₄]

  have l2 : (a * b) * (d * c) = 1 := by
    calc
      (a * b) * (d * c) = a * (b * d) * c := by rw [mul_assoc, mul_assoc, mul_assoc]
      _= a * 1 * c := by rw [h₃]
      _= 1 := by
        simp
        rw [h₁]
  exact ⟨d * c, l1, l2⟩


-- 5. ℕ be the set of natural numbers, and s : ℕ → ℕ be the shift map defined as s(n) = n + 1. Prove that s has no right inverse.

def s (n : Nat) : Nat := n + 1

example : ¬ ∃ (s₁ : Nat → Nat), ∀ (n : Nat), s (s₁ n) = n := by
  intro h
  rcases h with ⟨s₁, h⟩
  specialize h 0
  dsimp [s] at h
  exact Nat.succ_ne_zero _ h

-- 6. Let S be a set with an associative law of composition and with an identity element. Prove that the subset consisting of the invertible elements in S is a group.

example {α : Type} [Monoid α] : Group αˣ := by
  exact Units.instGroup

-- 7. Let x, y, z be elements of a group G. Suppose that xyz = 1, prove that yzx = 1

example {α : Type} [Group α] (x y z : α) (h₁ : x * y * z = 1) : y * z * x = 1 := by
  have l : y * z = x⁻¹ := by
    refine Eq.symm (DivisionMonoid.inv_eq_of_mul x (y * z) ?_)
    rw [←mul_assoc]
    exact h₁
  calc
    y * z * x = x⁻¹ * x := by rw [l]
    _= 1 := by simp

-- 8. Let G be a group and define an opposite group G^0 with the law of composition a * b = ba, prove that G^0 is still a group

def Opposite (α : Type) : Type := α

def Opposite.op {α : Type} (x : α) : Opposite α := x
def Opposite.unop {α : Type} (x : Opposite α) : α := x

instance {G : Type} [Group G] : Mul (Opposite G) where
  mul a b := (Opposite.unop b) * (Opposite.unop a)

instance {G : Type} [Group G] : One (Opposite G) where
  one := Opposite.op 1

instance {G : Type} [Group G] : Inv (Opposite G) where
  inv a := Opposite.op (Opposite.unop a)⁻¹

lemma unop_mul {G} [Group G] (a b : Opposite G) : a * b = b.unop * a.unop := rfl

lemma unop_inv {G} [Group G] (a : Opposite G) : (a⁻¹).unop = (a.unop)⁻¹ := rfl

lemma unop_G {G} [Group G] (a : G) : Opposite.unop a = a := rfl

variable {G : Type} [Group G]

instance : Group (Opposite G) where
  mul a b := (Opposite.unop b) * (Opposite.unop a)
  mul_assoc a b c := by
    calc
      a * b * c = c.unop * b.unop * a.unop := by
        rw [unop_mul a b]
        rw [unop_mul]
        rw [mul_assoc]
        rfl
      _= (c.unop * b.unop) * a.unop := by
        rw [mul_assoc]
      _= a * (b * c) := by
        rw [unop_mul]
        rw [unop_mul]
        rw [unop_G]
        rfl
  one_mul a := by
    calc
      (Opposite.op 1) * a = a.unop * 1 := by
        rw [unop_mul]
        rfl
      _= a.unop := by group
      _= a := rfl
  mul_one a := by
    calc
      a * (Opposite.op 1) = 1 * a.unop := by
        rw [unop_mul]
        rfl
      _= a.unop := by group
      _= a := rfl
  inv_mul_cancel := by
    intro a
    calc
      a⁻¹ * a = a.unop * (a⁻¹).unop := by
        rw [unop_mul, unop_inv]
      _= a.unop * (a.unop)⁻¹ := by
        rfl
      _= 1 := by group

-- 9. If a and b are positive integers whose sum is a prime p, their greatest common divisor is 1.

example (a b : PNat) (h₁ : Nat.Prime (a + b)) : (a : Nat).gcd b = 1 := by
  let d := (a : Nat).gcd b
  have d_div_a : d ∣ a := by
    exact Nat.gcd_dvd_left ↑a ↑b
  have d_div_b : d ∣ b := by
    exact Nat.gcd_dvd_right ↑a ↑b
  have d_div_sum : d ∣ (a + b) := by
    exact (Nat.dvd_add_iff_right d_div_a).mp d_div_b
  rw [Nat.prime_def] at h₁
  obtain ⟨hh₁, hh₂⟩ := h₁
  specialize hh₂ d
  specialize hh₂ d_div_sum
  rcases hh₂ with ha | hb
  · exact ha
  · have dga : a ≥ d := by
      refine Nat.gcd_le_left ↑b ?_
      exact PNat.pos a
    rw [hb] at dga
    have bl0 : (b : Nat) ≤ 0 := by
      exact Nat.le_of_add_le_add_left dga
    have bg0 : (b : Nat) > 0 := by
      exact PNat.pos b
    exfalso
    apply not_lt_of_le bl0 bg0


-- 10. Let a and b be elements of a group G. Assume that a has order 7 and that a^3b=ba^3. Prove that ab=ba

example {α : Type} [Group α] (a b : α) (h₁ : orderOf a = 7) (h₂ : a^3 * b = b * a^3) : b * a = a * b := by
  calc
    b * a = a^4 * b * a^4 := by
      rw [pow_add a 3 1, ← mul_assoc]
      simp
      rw [mul_assoc, ← h₂, ← mul_assoc, mul_assoc (a^3) (a) (a^3), ← pow_succ' a]
      simp
      rw [← pow_add a 3 4]
      simp
      rw [← pow_orderOf_eq_one a, h₁]
    _= a * a^3 * b * a^4 := by
      group
    _= a * b * a^3 * a^4 := by
      simp
      rw [mul_assoc, h₂, ← mul_assoc]
    _= a * b := by
      rw [mul_assoc, ← pow_add a 3 4]
      simp
      rw [← pow_orderOf_eq_one a, h₁]

-- 11. Let a and b be elements of a group G. Prove that ab and ba has the same order.

example {α : Type} [Group α] (a b : α) (n : PNat) (h : orderOf (b * a) = n): orderOf (a * b) = n := by
  rw [orderOf_eq_iff] at h
  rw [orderOf_eq_iff]
  constructor
  have h₁ : a * b = a * (b * a) * a⁻¹ := by
    refine Eq.symm (mul_inv_eq_of_eq_mul ?_)
    rw [mul_assoc]
  rw [h₁]
  have h₂ : (a * (b * a) * a⁻¹) ^ (n : Nat) = a * (b * a) ^ (n : Nat) * a⁻¹ := by
    rw [conj_pow]
  rw [h₂, h.1]
  simp
  intro m hh hh₁
  by_contra hh₂
  rcases h with ⟨hh₃, hh₄⟩
  specialize hh₄ m hh hh₁
  have l : b * a = b * (a * b) * b⁻¹ := by
    refine Eq.symm (mul_inv_eq_of_eq_mul ?_)
    rw [mul_assoc]
  have hh₅ : (b * a) ^ m = 1 := by
    calc
      (b * a) ^ m = (b * (a * b) * b⁻¹) ^ m := by
        rw [l]
      _= b * (a * b) ^ m * b⁻¹ := by
        rw [conj_pow]
      _= 1 := by
        rw [hh₂]
        simp
  contradiction
  exact PNat.pos n
  exact PNat.pos n

-- 12. Let φ : G → G' be a surjective homomorphism. Prove that if G is cyclic (abelian), then G' is cyclic (abelian)

example {G G' : Type*} [Group G] [Group G'] (f : G →* G') (h₁ : IsCyclic G) (h₂ : Function.Surjective f) : IsCyclic G' := by
  dsimp [Function.Surjective] at h₂
  apply exists_zpow_surjective at h₁
  refine { exists_zpow_surjective := ?_ }
  obtain ⟨g, hg⟩ := h₁
  use f g
  dsimp [Function.Surjective] at hg
  dsimp [Function.Surjective]
  intro a
  let ⟨c, hc⟩ := h₂ a
  let ⟨d, hd⟩ := hg c
  use d
  calc
    f g ^ d = f (g ^ d) := by
      exact Eq.symm (MonoidHom.map_zpow f g d)
    _= f c := by
      rw [hd]
    _= a := by
      rw [hc]

example {G G' : Type*} [CommGroup G] [Group G'] (f : G →* G') (h₂ : Function.Surjective f) : CommGroup G' := by
  dsimp [Function.Surjective] at h₂
  apply CommGroup.mk
  intro a b
  obtain ⟨a', ha'⟩ := h₂ a
  obtain ⟨b', hb'⟩ := h₂ b
  calc
    a * b = (f a') * (f b') := by
      rw [←ha', hb']
    _= f (a' * b') := by
      rw [f.map_mul a' b']
    _= f (b' * a') := by
      refine DFunLike.congr rfl ?_
      rw [mul_comm a' b']
    _= (f b') * (f a') := by
      rw [← f.map_mul b' a']
    _= b * a := by
      rw [hb', ha']

-- 13. Prove that the intersection K ∩ H of subgroup G is a subgroup of G.

example {G : Type} [Group G] (H K : Subgroup G) : H ⊓ K ≤ H := by
  exact inf_le_left -- the proof is basically a cheat

-- 14. Prove that the if K is a normal subgroup of G, then K ∩ H is a normal subgroup of H

example {G : Type} [Group G] (H K : Subgroup G) [K.Normal] : ((H ⊓ K).subgroupOf H).Normal := by
  simp
  exact Subgroup.normal_subgroupOf

-- 15. Let f : ℝ⁺ → ℂˣ be the map f(x) = eⁱˣ. Prove that f is a homomorphism.

-- the desired set
def complex_without_zero := { z : ℂ | z ≠ 0}

lemma mul_closed { a b : ℂ } (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  by_contra h
  rw [mul_eq_zero] at h
  cases h with
  | inl hp => exact ha hp
  | inr hp' => exact hb hp'

-- instance for multiplication on C*
instance : Mul complex_without_zero :=
  ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, mul_closed ha hb⟩⟩

instance : One complex_without_zero := ⟨1, one_ne_zero⟩

noncomputable instance : Inv complex_without_zero := ⟨fun ⟨z, hz⟩ => ⟨z⁻¹, inv_ne_zero hz⟩⟩

instance : Coe {x // x ∈ complex_without_zero} ℂ := ⟨Subtype.val⟩

@[simp] lemma coe_mul (x y : {x // x ∈ complex_without_zero}) :
  ↑(x * y) = (x : ℂ) * (y : ℂ) := rfl

@[simp] lemma coe_inv (x : {x // x ∈ complex_without_zero}) :
  ↑(x⁻¹) = (x : ℂ)⁻¹ := rfl

@[simp] lemma coe_one : ↑(1 : {x // x ∈ complex_without_zero}) = (1 : ℂ) := rfl

-- formally prove that C* is a commutative group
noncomputable instance : CommGroup complex_without_zero where
  mul_assoc := by
    rintro ⟨a, _⟩ ⟨b, _⟩  ⟨c, _⟩
    ext1
    exact mul_assoc a b c
  one_mul := by
    rintro ⟨a, _⟩
    ext1
    exact one_mul a
  mul_one := by
    rintro ⟨a, _⟩
    ext1
    exact mul_one a
  mul_comm := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    ext1
    exact mul_comm a b
  inv_mul_cancel := by
    intro a
    ext1
    simp only [coe_mul, coe_inv]
    rw [mul_comm]
    refine (mul_inv_eq_iff_eq_mul₀ ?_).mpr ?_
    dsimp [complex_without_zero] at a
    simp
    exact a.property
    rw [coe_one, one_mul]


-- formally prove that f is homomorphism

noncomputable instance : AddGroup ℝ := by infer_instance

noncomputable def expFun (x : ℝ) := Complex.exp (x * Complex.I)

example (x y : ℝ): (x + y) * Complex.I = x * Complex.I + y * Complex.I := by
  exact RightDistribClass.right_distrib (↑x) (↑y) Complex.I

noncomputable def expHom [AddGroup ℝ] : (Multiplicative ℝ) →* complex_without_zero :=
  {
    toFun x :=  ⟨Complex.exp (Multiplicative.toAdd x * Complex.I), Complex.exp_ne_zero _⟩
    map_one' := by
      ext1
      simp [Complex.exp_zero]
    map_mul' := by
      intro x y
      ext1
      simp only
      rw [toAdd_mul]
      calc
        Complex.exp (↑(Multiplicative.toAdd x + Multiplicative.toAdd y) * Complex.I) = Complex.exp (↑(Multiplicative.toAdd x) * Complex.I + ↑(Multiplicative.toAdd y) * Complex.I) := by
          rw [← RightDistribClass.right_distrib (↑(Multiplicative.toAdd x)) ↑(Multiplicative.toAdd y) Complex.I]
          simp
        _= Complex.exp (↑(Multiplicative.toAdd x) * Complex.I) * Complex.exp (↑(Multiplicative.toAdd y) * Complex.I) := by
          rw [Complex.exp_add]
  }
