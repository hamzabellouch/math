import OAI.Geometry.NodalSets.Elliptic.CorrugationGlobalError
import OAI.Geometry.NodalSets.Elliptic.CorrugationHighRegime

namespace OAI

namespace Yau.Geometry
open Yau.Jets Real
open scoped ContDiff
noncomputable section

theorem corrugation_actual_regime_errors (χ : Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcpt : HasCompactSupport χ)
    (hχrange : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) {D : ℝ} (hD : 0 < D)
    (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D*(χ z)^((7:ℝ)/8))
    {amp K G : ℝ} (hamp : 0 ≤ amp) (hamp1 : amp ≤ 1) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (s L : ℝ),
      0 ≤ s → 0 < L → ∀ k : ℕ,
      ∀ (a b : Coord →L[ℝ] ℝ) (y x u v : Coord),
      ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → ‖a.prod b‖ ≤ K →
      ‖metricConnection (g x) (fderiv ℝ g x)‖ ≤ G →
      let χ₀ := χ ((corrugationScale L k)⁻¹ • (x-y))
      let l := corrugationSlope amp (1/4)
        (corrugationCellRadius (corrugationFastMap (corrugationFrequency k) a b (x-y)))
      ∀ T : ℝ, 0 < T →
      (corrugationFrequency k*χ₀*l ≤ T →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤ C*s*corrugationLowErrorRate L T k) ∧
      (T < corrugationFrequency k*χ₀*l →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤
            C*s*corrugationHighErrorRate L T k*(corrugationFrequency k*χ₀*l)) := by
  obtain ⟨C,hC,hbound⟩ := corrugation_global_source_error_bound χ hχ hcpt hχrange hD hχD hamp hK hG
  refine ⟨C,hC,?_⟩
  intro g s L hs hL k a b y x u v hu hv hQ hΓ χ₀ l T hT
  have hχ0 : 0 ≤ χ₀ := (hχrange _).1
  have hχ1 : χ₀ ≤ 1 := (hχrange _).2
  have hl : 0 ≤ l := corrugationSlope_nonneg hamp (corrugationCellRadius_properties _).1
  have hl1 : l ≤ 1 := corrugationSlope_le_one hamp hamp1 (by norm_num) (by norm_num)
    (corrugationCellRadius_properties _).1
  have hb := hbound g s (corrugationFrequency k) (corrugationScale L k) hs
    (corrugationFrequency_positive k) (corrugationScale_positive hL k) a b y x u v hu hv hQ hΓ
  constructor
  · intro hreg
    exact hb.trans (mul_le_mul_of_nonneg_left
      (corrugationLowErrorRate_bounds hL T k hχ0 hχ1 hl hl1 hreg).1 (mul_nonneg hC.le hs))
  · intro hreg
    have h := hb.trans (mul_le_mul_of_nonneg_left
      (corrugationHighErrorRate_bounds hL hT k hχ0 hχ1 hl hl1 hreg).1 (mul_nonneg hC.le hs))
    exact h.trans_eq (by ring)

end
end Yau.Geometry

end OAI
