import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelTails

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem dyadicAnnulus_disjoint {d : ℕ} (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    Pairwise (Disjoint on dyadicAnnulus x r) := by
  have hsep {k l : ℕ} (hkl : k < l) : Disjoint (dyadicAnnulus x r k) (dyadicAnnulus x r l) := by
    apply Set.disjoint_left.mpr
    intro y hyk hyl
    have hp : (2 : ℝ) ^ (k + 1) ≤ 2 ^ l :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hkl)
    have hm := mul_le_mul_of_nonneg_left hp hr.le
    exact (not_lt_of_ge (hm.trans hyl.1)) hyk.2
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact hsep h
  · exact (hsep h).symm

theorem inverseDistancePow_exterior_integral_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    (∫ y in {y | r < dist x y}, inverseDistancePow (m + 1) x y ∂μ) ≤ 2 * (C * 2 ^ m / r) := by
  have hgeo : Summable (fun k : ℕ => (C * 2 ^ m / r) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hs : Summable (fun k : ℕ =>
      ∫ y in dyadicAnnulus x r k, ‖inverseDistancePow (m + 1) x y‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _)
      (fun k => inverseDistancePow_annular_integral_bound m C μ hg x r hr k) hgeo
  have hiu : IntegrableOn (inverseDistancePow (m + 1) x) (⋃ k, dyadicAnnulus x r k) μ :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun k => inverseDistancePow_integrableOn_annulus m (m + 1) C μ hg x r hr k) hs
  have hsub := exterior_subset_iUnion_dyadicAnnulus x r hr
  calc
    _ ≤ ∫ y in ⋃ k, dyadicAnnulus x r k, inverseDistancePow (m + 1) x y ∂μ :=
      setIntegral_mono_set hiu (Filter.Eventually.of_forall fun y => inverseDistancePow_nonneg _ _ _)
        (Filter.Eventually.of_forall fun y hy => hsub hy)
    _ = ∑' k, ∫ y in dyadicAnnulus x r k, ‖inverseDistancePow (m + 1) x y‖ ∂μ := by
      rw [integral_iUnion (dyadicAnnulus_measurable x r) (dyadicAnnulus_disjoint x r hr) hiu]
      simp only [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
    _ ≤ ∑' k : ℕ, (C * 2 ^ m / r) * (1 / 2 : ℝ) ^ k :=
      Summable.tsum_le_tsum (fun k => inverseDistancePow_annular_integral_bound m C μ hg x r hr k)
        hs hgeo
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      norm_num
      ring

end

end RieszRectifiability

end OAI
