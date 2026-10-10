import OAI.Geometry.RCD.Coordinates.CompactHeatGaugeNormalization
import OAI.Geometry.RCD.Coordinates.BoundedHeatLogRegular
import OAI.Geometry.RCD.Metric.CompactFactorL2

namespace OAI

/-! # Actual bounded regular extensions of the fixed-gauge heat potential -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem fixed_gauge_heat_regular
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S,ℝ)) (hF : ∀ y, 0 < F y)
    {ε δ s : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hs : δ ≤ s) (z : X)
    {Ω : Set X} (hΩ : IsCompact Ω) :
    ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X))
      (V : X → ℝ) (L C : ℝ≥0),
      IsWeakLaplacian (hausdorff n X) hX.quadratic u q ∧ LipschitzWith L V ∧
      (∀ x, |V x| ≤ C) ∧ (SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] V) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[(hausdorff n X).restrict Ω]
        hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z s) := by
  let m := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let t := ε*s/2
  have ht : 0 < t := div_pos (mul_pos hε (hδ.trans_le hs)) (by norm_num)
  obtain ⟨G,hG,hFG⟩ := hX.fixedGaugeScaledPotential_normalized hn p ν F hF hε hδ hs z
  obtain ⟨f,⟨A,hf⟩,he⟩ := hX.compact_heat_factor_L2 hn p ν ρ hρ hρ0 hB hν G
  have hp : ∀ x ∈ Ω, 0 < kernelHeat m Q hk t f x := by
    intro x _
    rw [← he t ht x]
    exact hX.compactHeatFactor_positive hn p ν G hG t ht x
  obtain ⟨u,q,U,L,C,hq,hU,hUC,hu,hur⟩ := hX.bounded_heat_log_regular hn p f A hf ht hΩ hp
  let c : ℝ≥0 := ⟨ε,hε.le⟩
  have hrep : SobolevSpace.toLp m Q (ε • u) =ᵐ[m] fun x => ε*U x := by
    filter_upwards [hu,Lp.coeFn_smul ε (SobolevSpace.toLp m Q u)] with x hx hy
    change SobolevSpace.toLp m Q (ε • u) x = ε*SobolevSpace.toLp m Q u x at hy
    rw [hy,hx]
  refine ⟨ε • u,ε • q,fun x => ε*U x,‖ε‖₊*L,c*C,hq.smul m Q ε,?_,?_,hrep,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := mul_le_mul_of_nonneg_left (hU.dist_le_mul x y) (abs_nonneg ε)
    simpa only [Real.dist_eq,← mul_sub,abs_mul,NNReal.coe_mul,coe_nnnorm,
      Real.norm_eq_abs,mul_assoc] using hh
  · intro x
    rw [abs_mul,abs_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left (hUC x) hε.le
  · filter_upwards [ae_restrict_of_ae hrep,ae_restrict_of_ae hu,hur] with x hx hy hz
    rw [hx,← hy,hz,← he t ht x]
    exact (hFG x).symm

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
