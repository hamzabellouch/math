import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Model

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation

section CosetCap
variable {G : Type*} [Group G] [Fintype G]

lemma sum_mul_le_of_leftCosetCap (f F : G → ℝ) (H : Subgroup G) (B : ℝ)
    (hcap : LeftCosetCap f H B) (hF : ∀ g, 0 ≤ F g)
    (hinv : ∀ (g : G) (h : H), F (g * h) = F g) :
    ∑ g, f g * F g ≤ B / Fintype.card G * ∑ g, F g := by
  classical
  have hsum (h : H) : ∑ g, f (g * h) * F g = ∑ g, f g * F g := by
    apply Fintype.sum_equiv (Equiv.mulRight (h : G))
    intro g
    change f (g * h) * F g = f (g * h) * F (g * h)
    rw [hinv]
  have havg : (Fintype.card H : ℝ) * (∑ g, f g * F g) =
      ∑ g, (∑ h : H, f (g * h)) * F g := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [hsum]
  have hc : (H.index : ℝ) * (Fintype.card H : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using H.index_mul_card)
  have hh : 0 < (Fintype.card H : ℝ) := by positivity
  have hg : 0 < (Fintype.card G : ℝ) := by positivity
  have hi : 0 < (H.index : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) H.index
    nlinarith
  have h : (Fintype.card H : ℝ) * (∑ g, f g * F g) ≤
      (B / H.index) * ∑ g, F g := by
    rw [havg, Finset.mul_sum]
    exact Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_right (hcap g) (hF g)
  calc
    ∑ g, f g * F g ≤ ((B / H.index) * ∑ g, F g) / Fintype.card H := by
      apply (le_div_iff₀ hh).mpr
      simpa only [mul_comm] using h
    _ = B / Fintype.card G * ∑ g, F g := by
      rw [← hc]
      field_simp

lemma norm_sum_weighted_sq_le {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (c : ι → ℂ) :
    ‖∑ i, (p i : ℂ) * c i‖ ^ 2 ≤ (∑ i, p i) * ∑ i, p i * ‖c i‖ ^ 2 := by
  have hn : ‖∑ i, (p i : ℂ) * c i‖ ≤ ∑ i, p i * ‖c i‖ := by
    calc
      _ ≤ ∑ i, ‖(p i : ℂ) * c i‖ := norm_sum_le _ _
      _ = _ := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp _)]
  have hnonneg : 0 ≤ ∑ i, p i * ‖c i‖ := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (norm_nonneg _)
  have hsq : (∑ i, p i * ‖c i‖) ^ 2 ≤ (∑ i, p i) * ∑ i, p i * ‖c i‖ ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · exact fun i _ => hp i
    · exact fun i _ => mul_nonneg (hp i) (sq_nonneg _)
    · intro i hi
      nlinarith
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hsq

end CosetCap
end PartialPermutation

end

end OAI
