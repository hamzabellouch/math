import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.NonpHomogenize

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance laurentHomogenizeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentHomogenizeAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance laurentHomogenizeAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
local instance laurentHomogenizeNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentHomogenizeNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

def laurentHomogenizeMonomial (m : M) : R →+ PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  (PowerSeries.monomial (δ m).toNat).toAddMonoidHom.comp
    {toFun := fun a => HahnSeries.single (κ m) (Torus.monomial v Ω m a)
     map_zero' := by simp
     map_add' a b := by simp only [Torus.monomial_add, HahnSeries.single_add]}

def laurentHomogenize : Torus v Ω →+ PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  Finsupp.liftAddHom (laurentHomogenizeMonomial v Ω δ κ)

@[simp] lemma laurentHomogenize_monomial (m : M) (a : R) :
    laurentHomogenize v Ω δ κ (Torus.monomial v Ω m a) =
      PowerSeries.monomial (δ m).toNat (HahnSeries.single (κ m) (Torus.monomial v Ω m a)) :=
  Finsupp.liftAddHom_apply_single _ _ _

lemma laurentHomogenize_coeff (f : Torus v Ω) (d : ℕ) (z : ℤ) (m : M) :
    (coeff d (laurentHomogenize v Ω δ κ f)).coeff z m =
      if d = (δ m).toNat ∧ z = κ m then f m else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [_root_.map_add, _root_.map_add, HahnSeries.coeff_add]
    simp only [Finsupp.add_apply, hf, hg]
    split_ifs <;> simp
  | single n a =>
    change (coeff d (laurentHomogenize v Ω δ κ (Torus.monomial v Ω n a))).coeff z m = _
    rw [laurentHomogenize_monomial, coeff_monomial]
    by_cases hm : m = n
    · subst n
      by_cases hd : d = (δ m).toNat
      · rw [ite_eq_left hd]
        by_cases hz : z = κ m <;> simp [hd, hz, Torus.monomial]
      · simp [hd]
    · by_cases hd : d = (δ n).toNat <;> by_cases hz : z = κ n <;>
        simp [hd, hz, Torus.monomial, Finsupp.single_eq_of_ne hm]

lemma laurentHomogenize_monomial_mul (m n : M) (a b : R)
    (hm : 0 ≤ δ m) (hn : 0 ≤ δ n) :
    laurentHomogenize v Ω δ κ (Torus.monomial v Ω m a * Torus.monomial v Ω n b) =
      laurentHomogenize v Ω δ κ (Torus.monomial v Ω m a) *
        laurentHomogenize v Ω δ κ (Torus.monomial v Ω n b) := by
  rw [Torus.monomial_mul_monomial, laurentHomogenize_monomial,
    laurentHomogenize_monomial, laurentHomogenize_monomial, monomial_mul_monomial,
    HahnSeries.single_mul_single, Torus.monomial_mul_monomial, map_add, map_add,
    Int.toNat_add hm hn]

lemma laurentHomogenize_mul (f g : Torus v Ω)
    (hf : ∀ m, f m ≠ 0 → 0 ≤ δ m) (hg : ∀ m, g m ≠ 0 → 0 ≤ δ m) :
    laurentHomogenize v Ω δ κ (f*g) =
      laurentHomogenize v Ω δ κ f * laurentHomogenize v Ω δ κ g := by
  classical
  calc
    _ = ∑ m ∈ f.support, ∑ n ∈ g.support,
        laurentHomogenize v Ω δ κ (Torus.monomial v Ω m (f m)*Torus.monomial v Ω n (g n)) := by
      have H (s : Finset M) (a : M → Torus v Ω) :
          laurentHomogenize v Ω δ κ (∑m∈s,a m)=∑m∈s,laurentHomogenize v Ω δ κ (a m) :=
        _root_.map_sum (laurentHomogenize v Ω δ κ) a s
      simp_rw [←H]
      congr 1
      simp_rw [←homo_mul_sum]
      rw [torus_sum_monomial, ←homo_sum_mul, torus_sum_monomial]
    _ = ∑ m ∈ f.support, ∑ n ∈ g.support,
        laurentHomogenize v Ω δ κ (Torus.monomial v Ω m (f m))*
        laurentHomogenize v Ω δ κ (Torus.monomial v Ω n (g n)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact laurentHomogenize_monomial_mul v Ω δ κ m n _ _
        (hf m (Finsupp.mem_support_iff.mp hm)) (hg n (Finsupp.mem_support_iff.mp hn))
    _ = _ := by
      simp_rw [←Finset.mul_sum]
      rw [←Finset.sum_mul]
      congr 1 <;> rw [←_root_.map_sum, torus_sum_monomial]

lemma laurentHomogenize_one : laurentHomogenize v Ω δ κ 1 = 1 := by
  change laurentHomogenize v Ω δ κ (Torus.monomial v Ω 0 1) = _
  rw [laurentHomogenize_monomial, _root_.map_zero, _root_.map_zero, Int.toNat_zero,
    monomial_zero_eq_C_apply]
  change C (HahnSeries.single 0 (1 : Torus v Ω)) = 1
  simp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
