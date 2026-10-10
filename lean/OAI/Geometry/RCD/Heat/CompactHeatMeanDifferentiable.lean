import OAI.Geometry.RCD.Heat.CompactHeatMeanLawLimit
import OAI.Geometry.RCD.Heat.HeatBridgeSecondDerivative

namespace OAI

/-! # Differentiability of actual bounded heat-bridge means -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem interpolationMean_differentiable
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (H : X →ᵇ ℝ) (k : ℕ) (t : Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (D.interpolationMean H k) t := by
  let m := hausdorff n X
  let q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let τ := ε k/4
  have hτ : 0 < τ := div_pos (hε k) (by norm_num)
  have ht : 0 < τ*(t:ℝ) := mul_pos hτ t.property.1
  have htτ : τ*(t:ℝ) < τ := by nlinarith [t.property.2]
  obtain ⟨f,_hf,hef⟩ := hX.compact_heat_factor_L2 hn p μ ρ₀ hm₀ hp₀ hC₀ hμ (D.left k)
  obtain ⟨g,_hg,heg⟩ := hX.compact_heat_factor_L2 hn p ν ρ₁ hm₁ hp₁ hC₁ hν (D.right k)
  have hHm : MemLp H ∞ m := memLp_top_of_bound H.continuous.aestronglyMeasurable ‖H‖
    (Eventually.of_forall H.norm_coe_le_norm)
  let W := hHm.toLp H
  have hd := (kernelHeat_bridge_pairing_hasDerivAt_variation m q hk W f g ht htτ).scomp
    (t:ℝ) ((hasDerivAt_id (t:ℝ)).const_mul τ)
  apply hd.differentiableAt.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds t.property.1 t.property.2] with s hs
  have hsf : 0 < τ*s := mul_pos hτ hs.1
  have hsg : 0 < τ-τ*s := by nlinarith [hs.2]
  have htime : τ-τ*s=ε k/4*(1-s) := by dsimp only [τ]; ring
  change D.interpolationMean H k s = ∫ x, W x*(kernelHeat m q hk (τ*s) f x *
    kernelHeat m q hk (τ-τ*s) g x) ∂m
  apply integral_congr_ae
  filter_upwards [hHm.coeFn_toLp] with x hx
  rw [hx,← hef _ hsf x,← heg _ hsg x]
  change H x*((∫ y, hX.canonicalHeatKernel hn p (ε k/4*s) x y*D.left k y ∂μ)*
    (∫ y, hX.canonicalHeatKernel hn p (ε k/4*(1-s)) x y*D.right k y ∂ν)) =
    H x*((∫ y, hX.canonicalHeatKernel hn p (τ*s) x y*D.left k y ∂μ)*
    (∫ y, hX.canonicalHeatKernel hn p (τ-τ*s) x y*D.right k y ∂ν))
  rw [htime]

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
