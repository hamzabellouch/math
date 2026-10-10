import OAI.Analysis.FiniteFactor.CrossedProduct.BoundaryEvent
import OAI.Analysis.FiniteFactor.CrossedProduct.ProjectionColumns
import OAI.Analysis.FiniteFactor.Coupling.BadEvents

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Every signed finite coefficient uses the actual D_j. Positive indices
use the exact later-floor exclusions; negative indices use antitonicity. -/
theorem sourceBoundary_cocycle_finite (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (ω : SourceBiasedSample) (he : ω ∈ sourceBoundaryEvent j)
    (hxc : ∀ i, sourceBiasedEndpoint (fun _ => false) ω i ∈ Set.Ico 0 1)
    (hyc : ∀ i, sourceBiasedEndpoint (fun _ => true) ω i ∈ Set.Ico 0 1)
    (hfx : finiteFloorSupport θ (sourceBiasedEndpoint (fun _ => false) ω))
    (hfy : finiteFloorSupport θ (sourceBiasedEndpoint (fun _ => true) ω))
    (k : ℤ) (hk : |(k : ℝ)| ≤ (sourceStageState j).K) :
    1/sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => false) ω) ≤ (sourceStageState j).D ∧
    sourceCocycle θ sourceLogWeight (-k) (sourceBiasedEndpoint (fun _ => true) ω) ≤ (sourceStageState j).D := by
  let x := sourceBiasedEndpoint (fun _ => false) ω
  let y := sourceBiasedEndpoint (fun _ => true) ω
  by_cases h0 : 0 ≤ k
  · have hK : (k : ℝ) ≤ (sourceStageState j).K := (le_abs_self _).trans hk
    have hz := sourceBoundary_floor_zero θ hθ j ω he hxc hyc k h0 hK
    have hxlog := sourceLog_finite_bound θ hθ j k hk x hxc (fun i hi => (hz i hi).1)
    have hylog := sourceLog_finite_bound θ hθ j (-k) (by simpa using hk) y hyc (fun i hi => (hz i hi).2)
    constructor
    · simp only [sourceCocycle,Real.exp_neg,one_div,inv_inv]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans hxlog)
    · exact Real.exp_le_exp.mpr ((neg_le_abs _).trans hylog)
  · have hk0 : k ≤ 0 := le_of_not_ge h0
    have hD : (1 : ℝ) ≤ (sourceStageState j).D :=
      Real.one_le_exp (mul_nonneg (by positivity) (sourceStageState j).B_nonneg)
    constructor
    · have hh := sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfx hk0
      dsimp only at hh
      rw [sourceCocycle_zero θ sourceLogWeight hxc] at hh
      have hle : 1/sourceCocycle θ sourceLogWeight k x ≤ 1 := by
        simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hh
      exact hle.trans hD
    · have hh := sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfy
        (show (0 : ℤ) ≤ -k by omega)
      dsimp only at hh
      rw [sourceCocycle_zero θ sourceLogWeight hyc] at hh
      exact hh.trans hD

/-- Finite coefficient bounds for the arbitrary projection in the original
algebra, on the actual source boundary-exclusion event. -/
theorem sourceProjection_finite_coefficients (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceBoundaryEvent j → ∀ k : ℤ,
      |(k : ℝ)| ≤ (sourceStageState j).K →
      ‖sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω) k‖ ≤ (sourceStageState j).D ∧
      ‖sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω) k‖ ≤ (sourceStageState j).D := by
  have hcube := CouplingParameters.vectorEndpoint_unitCube
    (fun i : SourceCoordinate => stagedCouplingParameters j i.1)
  filter_upwards [
    ae_of_ae_map (sourceBiasedEndpoint_measurable (fun _ => false)).aemeasurable (hcube (fun _ => false)),
    ae_of_ae_map (sourceBiasedEndpoint_measurable (fun _ => true)).aemeasurable (hcube (fun _ => true)),
    sourceBiasedEndpoint_ae j (fun _ => false) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => true) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => false) (sourceProjection_columns_norm θ hp hproj),
    sourceBiasedEndpoint_ae j (fun _ => true) (sourceProjection_columns_norm θ hp hproj)]
    with ω hxc hyc hfx hfy hnx hny
  intro he k hk
  obtain ⟨hx,hy⟩ := sourceBoundary_cocycle_finite θ hθ j ω he hxc hyc hfx hfy k hk
  have hξ := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (sourceProjectionColumn p (sourceBiasedEndpoint (fun _ => false) ω)) k).trans hnx.1
  have hγ := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (sourceComplementColumn p (sourceBiasedEndpoint (fun _ => true) ω)) (-k)).trans hny.2
  constructor
  · simp only [sourceProjectionLeftCoefficient,leftCoefficient,norm_div,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (sourceCocycle_pos ..)]
    exact (div_le_div_of_nonneg_right hξ (sourceCocycle_pos ..).le).trans hx
  · simp only [sourceProjectionRightCoefficient,rightCoefficient,norm_mul,RCLike.norm_conj,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sourceCocycle_pos ..)]
    exact ((mul_le_mul_of_nonneg_left hγ (sourceCocycle_pos ..).le).trans_eq (mul_one _)).trans hy

end
end FiniteFactor

end OAI
