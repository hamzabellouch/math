import OAI.Geometry.RCD.Metric.CompactFactorInitialValue
import OAI.Geometry.RCD.Heat.CompactHeatScalingData
import OAI.Geometry.RCD.Metric.SubtypeDensitySupport

namespace OAI

/-! # The initial heat-factor product is the prescribed endpoint density -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
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

theorem initial_heat_product (ρ : X → ℝ) (hm : Measurable ρ) (hp : ∀ x, 0 ≤ ρ x)
    {C : ℝ≥0} (hC : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ C)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (k : ℕ) (f g : Lp ℝ 2 (hausdorff n X))
    (hf : ∀ (s : ℝ) (hs : 0 < s) (x : X),
      hX.compactHeatFactor hn p μ (D.left k) s hs x =
        kernelHeat (hausdorff n X) hX.quadratic (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f x)
    (hg : ∀ (s : ℝ) (hs : 0 < s) (x : X),
      hX.compactHeatFactor hn p ν (D.right k) s hs x =
        kernelHeat (hausdorff n X) hX.quadratic (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s g x) :
    (fun x => f x*heatAt (hausdorff n X) hX.quadratic (ε k/4) g x) =ᵐ[hausdorff n X] ρ := by
  let m := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  have hS : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  have hfi := hX.compact_heat_factor_initial_value hn p μ ρ hm hC (D.left k) f
    (fun s hs x => (hf s hs x).symm) hμ hp
  have hoff := subtype_density_zero_off hS.measurableSet m μ ρ hm hp hμ
  have hc : 0 < ε k/4 := div_pos (hε k) (by norm_num)
  filter_upwards [hfi,hoff,kernelHeat_represents_L2 m Q hk hc g] with x hfx hzero hgx
  rw [hfx,← hgx,← hg (ε k/4) hc x]
  by_cases hx : x ∈ S
  · have hrow := D.row k ⟨x,hx⟩
    rw [show compactFactorExtension (D.left k) x = D.left k ⟨x,hx⟩ from
      compactFactorExtension_coe _ ⟨x,hx⟩]
    change ρ x*D.left k ⟨x,hx⟩*(∫ b, hX.canonicalHeatKernel hn p (ε k/4) x b*D.right k b ∂ν) = ρ x
    rw [mul_assoc,hrow,mul_one]
  · rw [hzero hx,zero_mul,zero_mul]

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
