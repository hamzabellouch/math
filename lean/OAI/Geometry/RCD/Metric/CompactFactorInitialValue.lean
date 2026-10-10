import OAI.Geometry.RCD.Heat.KernelHeatInitialUniqueness
import OAI.Geometry.RCD.Metric.CompactFactorL2

namespace OAI

/-! # Identification of the initial datum of a compact heat factor -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_initial_value {S : Set X} [CompactSpace S]
    (ν : Measure S) (ρ : X → ℝ) (hρ : Measurable ρ) {C : ℝ≥0}
    (hC : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ C)
    (F : C(S,ℝ)) (f : Lp ℝ 2 (hausdorff n X))
    (hrep : ∀ t : ℝ, 0 < t → ∀ x,
      kernelHeat (hausdorff n X) hX.quadratic
        (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t f x =
      ∫ a, hX.canonicalHeatKernel hn p t x a*F a ∂ν)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hρ0 : ∀ x, 0 ≤ ρ x) :
    f =ᵐ[hausdorff n X] fun x => ρ x*compactFactorExtension F x := by
  let m := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  have hS : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  have hm := compact_weighted_density_memLp hS F m hρ hC
  let g := hm.toLp _
  have hg : g =ᵐ[m] fun x => ρ x*compactFactorExtension F x := hm.coeFn_toLp
  have hfg : f = g := kernelHeat_initial_unique m Q hk f g (by
    intro t ht x
    rw [hrep t ht x,kernelHeat_eq_integral m Q hk ht g x]
    rw [compact_weighted_density_integral hS.measurableSet m ν ρ hρ hρ0 hν F]
    apply integral_congr_ae
    filter_upwards [hg] with y hy
    rw [hy])
  exact hfg ▸ hg

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
