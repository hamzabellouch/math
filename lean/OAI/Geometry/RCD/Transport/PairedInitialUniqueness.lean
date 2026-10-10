import OAI.Geometry.RCD.Transport.PairedInitialObstruction
import OAI.Geometry.RCD.Metric.SeparatedPairRestriction

namespace OAI

/-! # The initial point determines a compressed optimal path almost everywhere -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem paired_common_initial_unique (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ]
    (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π)
    (hinit : ∀ᵐ z ∂σ, z.1 0=z.2 0)
    : ∀ᵐ z ∂σ, z.1=z.2 := by
  by_contra hbad
  have hneq : σ {z | z.1 ≠ z.2} ≠ 0 := by simpa only [ae_iff] using hbad
  have hpos : 0 < σ.real {z | z.1 ≠ z.2} :=
    ENNReal.toReal_pos hneq (measure_ne_top _ _)
  obtain ⟨S,_,hm,hsing⟩ := exists_separated_restriction σ measurable_fst measurable_snd hpos
  let τ := σ.restrict S
  have hτ0 : τ univ ≠ 0 := by
    have hh : 0 < τ.real univ := (div_pos hpos (by norm_num)).trans hm
    intro he
    simp [Measure.real,he] at hh
  have hτinit : ∀ᵐ z ∂τ, z.1 0=z.2 0 :=
    hinit.filter_mono Measure.restrict_le_self.absolutelyContinuous.ae_le
  exact hX.paired_initial_obstruction hn p hR π hg hp hC hc hs₀ hs₁ τ hτ0
    ((Measure.map_mono Measure.restrict_le_self measurable_fst).trans hl)
    ((Measure.map_mono Measure.restrict_le_self measurable_snd).trans hr) hτinit hsing

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
