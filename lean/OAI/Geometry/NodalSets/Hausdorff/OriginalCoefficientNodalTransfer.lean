import OAI.Geometry.NodalSets.Coefficients.OriginalCoefficientComparison
import OAI.Geometry.NodalSets.Spectral.TargetUniformProjection

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory Yau.Jets
open scoped ContDiff NNReal ENNReal
noncomputable section

lemma uniform_original_coefficient_nodal_transfer
    (a b r R : ℝ) (ha : 0 < a) (hb : 0 < b) (hr0 : 0 < r) (hR0 : 0 < R)
    (p : Manifold5) (s : ℝ) {t : ℝ} (ht : t ≠ 0) {K : Set (Coord × ℝ)}
    (hK : IsCompact K) (hKD : K ⊆ productChartDomain p s t) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
        (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
        (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
        (hrp : ∀ x, 0 < rho x),
        (∀ x v, a * ‖v‖^2 ≤ ambientMatrixForm (A x) v v) →
        (∀ x v, ambientMatrixForm (A x) v v ≤ b * ‖v‖^2) →
        (∀ x, r ≤ rho x) → (∀ x, rho x ≤ R) →
        ∀ (u : Manifold5 → ℝ) (Z : Set (Coord × ℝ)), Z ⊆ K →
          (∀ z ∈ Z, u (productChartInverse p s t z) = 0) →
          Measure.hausdorffMeasure (4:ℝ) Z ≤ (C:ℝ≥0∞)^4 *
            nodalMeasure (independentAmbientMetric A rho hA hp hr hrp) u := by
  let c := min (r/b) (a^5/R^2)
  have hc : 0 < c := (coefficient_comparison_constants_pos a b r R ha hb hr0 hR0).1
  let L : ℝ≥0 := ⟨(Real.sqrt c)⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg c)⟩
  have hL : 0 < L := inv_pos.mpr (Real.sqrt_pos.mpr hc)
  have he : (L:ℝ)^2 * c = 1 := by
    change ((Real.sqrt c)⁻¹)^2 * c = 1
    rw [inv_pow, Real.sq_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  dsimp only [c] at he
  obtain ⟨C,hC,hbound⟩ := uniform_compact_coordinate_nodal_transfer
    roundProductMetric L hL p s ht hK hKD
  refine ⟨C,hC,?_⟩
  intro A rho hA hp hr hrp hlo hhi hrho hR
  apply hbound
  intro x v
  have h := (independentAmbientMetric_original_comparison a b r R ha hb hr0
    A rho hA hp hr hrp hlo hhi hrho hR x v).1
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (L:ℝ))
  simpa only [← mul_assoc, he, one_mul] using hh

end
end Yau.Target

end OAI
