import OAI.NumberTheory.TwoPoint.Walks.ManyUnlitCatalog
import OAI.NumberTheory.TwoPoint.Walks.GoodWordWeightedSum

namespace OAI

/-! Finite designation catalogs may be indexed by numerical words of varying length. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

/-- Each admissible designation set is a subset of all slots. The complete
catalog therefore costs at most one binary choice per slot. -/
lemma designation_catalog_weight {I τ : Type*} [DecidableEq I] [Fintype τ]
    (F : Finset I) (allowed : I → Finset (Finset τ)) (weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) :
    (∑ a ∈ F.sigma allowed, weight a.1) ≤
      (2 : ℝ) ^ Fintype.card τ * ∑ i ∈ F, weight i := by
  rw [sum_sigma]
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have hc : (allowed i).card ≤ 2 ^ Fintype.card τ := by
    exact (card_le_card (subset_univ _)).trans_eq (by simp)
  simp only [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hw i)

/-- The threshold is uniform in the finite catalog and in its index type.
It can therefore be used for word lengths and prime pools varying with L. -/
theorem eventually_many_unlit_finsets (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (I : Type) [DecidableEq I] (F : Finset I)
      (E : I → ℕ) (H : ℝ) (weight : I → ℝ),
      (∀ i ∈ F, 0 ≤ weight i) →
      (∑ i ∈ F, weight i) ≤ Real.exp (C * L * (Real.log L) ^ 2) →
      (∀ i ∈ F, L ^ (1 / 50 : ℝ) ≤ 2 * E i) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∑ i ∈ F, weight i * (H⁻¹) ^ E i) ≤ Real.exp (-L ^ (101 / 100 : ℝ)) := by
  filter_upwards [eventually_many_unlit_decay C hC] with L hdecay
  intro I _ F E H weight hw hmass hE hH
  let scale := Real.exp (C * L * (Real.log L) ^ 2)
  let target := Real.exp (-L ^ (101 / 100 : ℝ))
  have hs : 0 < scale := Real.exp_pos _
  have hi (i) (hmem : i ∈ F) : (H⁻¹) ^ E i ≤ target / scale := by
    apply (le_div_iff₀ hs).mpr
    simpa only [mul_comm] using hdecay (E i) H (hE i hmem) hH
  calc
    _ ≤ ∑ i ∈ F, weight i * (target / scale) :=
      sum_le_sum (fun i hmem => mul_le_mul_of_nonneg_left (hi i hmem) (hw i hmem))
    _ = (∑ i ∈ F, weight i) * (target / scale) := (sum_mul _ _ _).symm
    _ ≤ scale * (target / scale) := mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = _ := mul_div_cancel₀ _ hs.ne'

end TwoPointCorrelations

end OAI
