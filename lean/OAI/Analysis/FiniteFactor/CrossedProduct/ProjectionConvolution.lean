import OAI.Analysis.FiniteFactor.CrossedProduct.ProjectionColumns
import OAI.Analysis.FiniteFactor.CrossedProduct.ConvolutionCocycle
import OAI.Analysis.FiniteFactor.Fiber.TransportConvolution

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ComplexConjugate ENNReal
noncomputable section

/-- The original coefficient sequences satisfy every nonnegative convolution
identity under the actual augmented biased law, with absolute sum at most one.
This instantiates the range and weight hypotheses from the constructed algebra. -/
theorem sourceProjection_convolution (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ∀ n : ℕ,
      (∑' k : ℤ, sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω) k *
        sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω) (-(n : ℤ)-k)) = 0 ∧
      Summable (fun k : ℤ => ‖sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω) k *
        sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω) (-(n : ℤ)-k)‖) ∧
      (∑' k : ℤ, ‖sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω) k *
        sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω) (-(n : ℤ)-k)‖) ≤ 1 := by
  let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
  have hInv : ∀ᵐ y ∂sourceBaseMeasure, ∀ n : ℕ,
      (1-sourceOperatorField p y)*sourceOperatorField (T^n) y*sourceOperatorField p y = 0 := by
    apply ae_all_iff.mpr
    intro n
    exact sourceOperatorField_invariant θ hp (pow_mem (staged_sourceOperator_mem θ hθ) n)
      (invariant_projection_pow p T hproj.isIdempotentElem hinv n)
  have hAct := ae_all_iff.mpr (sourceOperatorField_sourceOperator_pow θ hθ)
  filter_upwards [sourceProjection_biased_ratio_augmented θ hθ hs hp hproj hinv j,
    sourceBiasedEndpoint_ae j (fun _ => false) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => true) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedLaw_ordered j,
    sourceBiasedEndpoint_ae j (fun _ => true) (sourceOperatorField_projection θ hp hproj),
    sourceBiasedEndpoint_ae j (fun _ => true) hInv,
    sourceBiasedEndpoint_ae j (fun _ => true) hAct,
    sourceBiasedEndpoint_ae j (fun _ => false) (sourceProjection_columns_norm θ hp hproj),
    sourceBiasedEndpoint_ae j (fun _ => true) (sourceProjection_columns_norm θ hp hproj)]
    with ω hD hfx hfy hord hPy hi ha hnx hny
  intro n
  let x := sourceBiasedEndpoint (fun _ => false) ω
  let y := sourceBiasedEndpoint (fun _ => true) ω
  have hxy : ∀ i, x i ≤ y i := hord
  obtain ⟨D,_hDn,hDa,hd⟩ := hD
  have hz : (∑' k : ℤ, sourceProjectionLeftCoefficient θ p x k *
      sourceProjectionRightCoefficient θ p y (-(n : ℤ)-k)) = 0 := by
    apply fiber_transport_convolution_zero (sourceOperatorField p x) (sourceOperatorField p y) D
      (sourceOperatorField (T^n) y) hPy
      (fun k => sourceCocycle θ sourceLogWeight k x) (fun k => sourceCocycle θ sourceLogWeight k y)
      (fun k => ne_of_gt (sourceCocycle_pos ..)) (n : ℤ) hd (hi n) hDa
    intro v k
    have hk : (n : ℤ)+k-(n : ℤ) = k := by omega
    rw [ha n v ((n : ℤ)+k),hk,sourceCocycle_power_weight θ sourceLogWeight hfy n k,Complex.ofReal_div]
  obtain ⟨habs,hbound⟩ := cocycle_convolution_absolute_convergence
    (sourceProjectionColumn p x) (sourceComplementColumn p y)
    (fun k => sourceCocycle_pos θ sourceLogWeight k x)
    (fun k => sourceCocycle_pos θ sourceLogWeight k y)
    (sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfx)
    (sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfy)
    (sourceCocycle_ordered θ sourceLogWeight sourceLogWeight_nonneg hfx hfy hxy)
    (n := (n : ℤ)) (by omega)
  refine ⟨hz,habs,hbound.trans ?_⟩
  exact (mul_le_mul hnx.1 hny.2 (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

end
end FiniteFactor

end OAI
