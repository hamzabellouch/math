import OAI.Geometry.RCD.Metric.CompactFactorL2

namespace OAI

/-! # Nonnegative initial data for the positive compact heat factors

Positivity at every positive heat time passes to the original L² datum by
strong continuity at zero.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_nonnegative_data {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (ρ : X → ℝ)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0≤ρ x) {C : ℝ≥0}
    (hC : ∀ᵐ x ∂hausdorff n X, |ρ x|≤C)
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (hF : ∀ a, 0<F a) :
    ∃ f : Lp ℝ 2 (hausdorff n X), 0≤f ∧ HasBoundedAmplitude f ∧
      ∀ (t : ℝ) (ht : 0<t) (x : X), hX.compactHeatFactor hn p ν F t ht x=
        kernelHeat (hausdorff n X) hX.quadratic
          (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t f x := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨f,hf,he⟩ := hX.compact_heat_factor_L2 hn p ν ρ hρ hρ0 hC hν F
  have htpos (t : ℝ) (ht : 0<t) : 0≤heatAt μ Q t f := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [kernelHeat_represents_L2 μ Q hk ht f] with x hx
    rw [←hx,←he t ht x]
    exact (hX.compactHeatFactor_positive hn p ν F hF t ht x).le
  let e : ℕ → ℝ := fun i => 1/(i+1:ℝ)
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun i => heatAt μ Q (e i) f) atTop (𝓝 f) := by
    have hh := ((heatAt_continuous μ Q f).tendsto 0).comp he0
    rw [heatAt_zero,one_apply_eq_self] at hh
    exact hh
  have hf0 : 0≤f := ge_of_tendsto ht (.of_forall fun i => htpos (e i) (by dsimp only [e]; positivity))
  exact ⟨f,hf0,hf,he⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
