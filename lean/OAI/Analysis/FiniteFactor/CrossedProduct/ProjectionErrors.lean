import OAI.Analysis.FiniteFactor.CrossedProduct.ProjectionEvent
import OAI.Analysis.FiniteFactor.CrossedProduct.ProjectionConvolution
import OAI.Analysis.FiniteFactor.CrossedProduct.MaskedError
import OAI.Analysis.FiniteFactor.CrossedProduct.OmittedRatio
import OAI.Analysis.FiniteFactor.Truncation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Exchange the coefficient and sample viewpoints of the same mask. -/
theorem indicator_swap {ι Ω : Type*} (H : ι → Set Ω) (f : ι → Ω → ℝ) (i : ι) (ω : Ω) :
    {k | ω ∈ H k}.indicator (fun k => f k ω) i = (H i).indicator (f i) ω := by
  classical
  by_cases h : ω ∈ H i
  · rw [Set.indicator_of_mem (show i ∈ {k | ω ∈ H k} from h),Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (show i ∉ {k | ω ∈ H k} from h),Set.indicator_of_notMem h]

def sourceTruncatedCoefficient (θ : SourceCoordinate → ℝ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (j : ℕ) (n : ℤ)
    (ω : SourceBiasedSample) : ℂ :=
  laurentProductCoefficient (sourceStageState j).K
    (sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω))
    (sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω)) (-n)

def sourceOmittedError (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n : ℤ) (b : Bool) (ω : SourceBiasedSample) : ℝ :=
  ∑' k : ℤ, (sourceOmittedBadEvent θ hθ j hphase n k b).indicator
    (fun ω => ‖sourceProjectionColumn p (sourceBiasedEndpoint (fun _ => false) ω) k‖ *
      ‖sourceComplementColumn p (sourceBiasedEndpoint (fun _ => true) ω) (n+k)‖) ω

theorem sourceOmittedError_nonneg (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n : ℤ) (b : Bool) (ω) :
    0 ≤ sourceOmittedError θ hθ p j hphase n b ω :=
  tsum_nonneg (fun _k => Set.indicator_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) ω)

/-- Both actual infinite error sums are integrable and have the source bound. -/
theorem sourceOmittedError_estimate (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n : ℤ) (b : Bool) :
    Integrable (sourceOmittedError θ hθ p j hphase n b) (sourceBiasedLaw j) ∧
      (∫ ω, sourceOmittedError θ hθ p j hphase n b ω ∂sourceBiasedLaw j) ≤ Real.exp (-(sourceStage j).L/800) := by
  unfold sourceOmittedError
  cases b
  · simpa only [sourceOmittedError,sourceColumn,Bool.false_eq_true,↓reduceIte,Bool.not_false,zero_add] using
      sourceOmitted_masked_error θ hθ hp hproj j hphase n 0 n false
  · simpa only [sourceOmittedError,sourceColumn,Bool.false_eq_true,↓reduceIte,Bool.not_true,zero_add,mul_comm] using
      sourceOmitted_masked_error θ hθ hp hproj j hphase n n 0 true

theorem sourceProjectionEvent_error_pointwise (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceProjectionEvent p j →
      ‖sourceTruncatedCoefficient θ p j n ω‖ ≤ Real.exp (-(sourceStage j).L) +
        sourceOmittedError θ hθ p j hphase n false ω + sourceOmittedError θ hθ p j hphase n true ω := by
  let H := fun b v => sourceOmittedBadEvent θ hθ j hphase (n : ℤ) v b
  have hratio : ∀ᵐ ω ∂sourceBiasedLaw j, ∀ v : ℤ,
      v ∉ convolutionWindow (sourceStageState j).K n → ω ∈ sourceTagEndpointEvent j →
      sourceCocycle θ sourceLogWeight ((n : ℤ)+v) (sourceBiasedEndpoint (fun _ => true) ω) /
        sourceCocycle θ sourceLogWeight v (sourceBiasedEndpoint (fun _ => false) ω) ≤
        Real.exp (-(sourceStage j).L)+(H false v).indicator (fun _ => (1 : ℝ)) ω+
          (H true v).indicator (fun _ => (1 : ℝ)) ω := by
    apply ae_all_iff.mpr
    intro v
    by_cases hv : v ∉ convolutionWindow (sourceStageState j).K n
    · exact (sourceOmitted_ratio_bound θ hθ j hphase n v (by omega)
        ((not_mem_convolutionWindow _ _ _).mp hv)).mono (fun ω h _ => h)
    · exact Eventually.of_forall (fun ω h => (hv h).elim)
  filter_upwards [hratio,sourceProjection_convolution θ hθ hs hp hproj hinv j,
    sourceTaggedEvent_endpoints j,sourceBiasedLaw_ordered j,
    sourceBiasedEndpoint_ae j (fun _ => false) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => true) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => false) (sourceProjection_columns_norm θ hp hproj),
    sourceBiasedEndpoint_ae j (fun _ => true) (sourceProjection_columns_norm θ hp hproj)]
    with ω hr hc ht hxy hfx hfy hnx hny
  intro he
  let x := sourceBiasedEndpoint (fun _ => false) ω
  let y := sourceBiasedEndpoint (fun _ => true) ω
  have hind (b : Bool) (v : ℤ) :
      {k | ω ∈ H b k}.indicator (fun _ => (1 : ℝ)) v = (H b v).indicator (fun _ => (1 : ℝ)) ω :=
    indicator_swap (H b) (fun _ _ => (1 : ℝ)) v ω
  have hmask (b : Bool) (v : ℤ) :
      {k | ω ∈ H b k}.indicator
        (fun k => ‖sourceProjectionColumn p x k‖*‖sourceComplementColumn p y ((n : ℤ)+k)‖) v =
      (H b v).indicator (fun ω =>
        ‖sourceProjectionColumn p (sourceBiasedEndpoint (fun _ => false) ω) v‖*
          ‖sourceComplementColumn p (sourceBiasedEndpoint (fun _ => true) ω) ((n : ℤ)+v)‖) ω := by
    by_cases h : ω ∈ H b v
    · rw [Set.indicator_of_mem (show v ∈ {k | ω ∈ H b k} from h),Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (show v ∉ {k | ω ∈ H b k} from h),Set.indicator_of_notMem h]
  have hh := laurent_error_pointwise (sourceStageState j).K (n : ℤ)
    (sourceProjectionColumn p x) (sourceComplementColumn p y)
    (fun k => sourceCocycle_pos θ sourceLogWeight k x) (fun k => sourceCocycle_pos θ sourceLogWeight k y)
    (sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfx)
    (sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfy)
    (sourceCocycle_ordered θ sourceLogWeight sourceLogWeight_nonneg hfx hfy hxy)
    (by omega : (0 : ℤ) ≤ n) (H₁ := {v | ω ∈ H false v}) (H₂ := {v | ω ∈ H true v})
    (Real.exp_pos (-(sourceStage j).L)).le (hc n).1
    (fun v hv => by rw [hind false v,hind true v]; exact hr v hv (ht he.1.1))
  simp_rw [hmask] at hh
  change ‖sourceTruncatedCoefficient θ p j n ω‖ ≤
    Real.exp (-(sourceStage j).L)*(‖sourceProjectionColumn p x‖*‖sourceComplementColumn p y‖)+
      sourceOmittedError θ hθ p j hphase n false ω+sourceOmittedError θ hθ p j hphase n true ω at hh
  have hnorm : ‖sourceProjectionColumn p x‖*‖sourceComplementColumn p y‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hnx.1 hny.2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hbound := mul_le_mul_of_nonneg_left hnorm (Real.exp_pos (-(sourceStage j).L)).le
  linarith

end
end FiniteFactor

end OAI
