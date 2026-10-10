import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.TailBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

def closedExterior {d : ℕ} (a : Ambient d) (R : ℝ) : Set (Ambient d) :=
  {y | R ≤ dist a y}

theorem closedExterior_measurable {d : ℕ} (a : Ambient d) (R : ℝ) :
    MeasurableSet (closedExterior a R) :=
  measurableSet_le measurable_const (continuous_const.dist continuous_id).measurable

theorem closedExterior_subset_iUnion_dyadicAnnulus {d : ℕ}
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    closedExterior a R ⊆ ⋃ k : ℕ, dyadicAnnulus a R k := by
  intro y hy
  have hratio : 1 ≤ dist a y / R := (le_div_iff₀ hR).mpr (by simpa using! hy)
  obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  refine mem_iUnion.mpr ⟨k, ?_, ?_⟩
  · simpa only [mul_comm] using! (le_div_iff₀ hR).mp hk₁
  · simpa only [mul_comm] using! (div_lt_iff₀ hR).mp hk₂

theorem iUnion_dyadicAnnulus_closedExterior {d : ℕ} (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    (⋃ k : ℕ, dyadicAnnulus a R k) = closedExterior a R := by
  apply Set.Subset.antisymm _ (closedExterior_subset_iUnion_dyadicAnnulus a R hR)
  intro y hy
  obtain ⟨k, hk⟩ := mem_iUnion.mp hy
  have hlow : R ≤ R * (2 : ℝ) ^ k := by
    simpa only [mul_one] using!
      mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
  exact hlow.trans hk.1

theorem inverseDistancePow_closedExterior_integrable_and_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (inverseDistancePow (m + 1) a) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, inverseDistancePow (m + 1) a y ∂μ) ≤ 2 * (C * 2 ^ m / R) := by
  have hgeo : Summable (fun k : ℕ => (C * 2 ^ m / R) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hs : Summable (fun k : ℕ =>
      ∫ y in dyadicAnnulus a R k, ‖inverseDistancePow (m + 1) a y‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _)
      (fun k => inverseDistancePow_annular_integral_bound m C μ hg a R hR k) hgeo
  have hiu : IntegrableOn (inverseDistancePow (m + 1) a) (⋃ k, dyadicAnnulus a R k) μ :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun k => inverseDistancePow_integrableOn_annulus m (m + 1) C μ hg a R hR k) hs
  refine ⟨by simpa only [iUnion_dyadicAnnulus_closedExterior a R hR] using! hiu, ?_⟩
  calc
    _ = ∑' k, ∫ y in dyadicAnnulus a R k, ‖inverseDistancePow (m + 1) a y‖ ∂μ := by
      rw [← iUnion_dyadicAnnulus_closedExterior a R hR,
        integral_iUnion (dyadicAnnulus_measurable a R) (dyadicAnnulus_disjoint a R hR) hiu]
      simp only [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
    _ ≤ ∑' k : ℕ, (C * 2 ^ m / R) * (1 / 2 : ℝ) ^ k :=
      Summable.tsum_le_tsum (fun k => inverseDistancePow_annular_integral_bound m C μ hg a R hR k)
        hs hgeo
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      norm_num
      ring

end

end RieszRectifiability

end OAI
