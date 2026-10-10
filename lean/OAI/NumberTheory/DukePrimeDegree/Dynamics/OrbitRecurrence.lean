import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact

namespace OAI

/-!
# Recurrence with close orbit parameters

For the exceptional-return argument, recurrence is needed in the parameter
topology of an orbit, which need not be closed in the ambient quotient.
A countable cover by compact parameter neighborhoods makes their images
measurable, and ordinary Poincaré recurrence supplies the required return.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [SecondCountableTopology G]
variable [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

omit [SecondCountableTopology G] in
lemma exists_compact_close_parameter_neighborhood (U : Set G) (hU : U ∈ 𝓝 1) (g : G) :
    ∃ K : Set G, IsCompact K ∧ K ∈ 𝓝 g ∧ ∀ a ∈ K, ∀ b ∈ K, a⁻¹ * b ∈ U := by
  have hc : Continuous (fun p : G × G => p.1⁻¹ * p.2) := continuous_fst.inv.mul continuous_snd
  have ht : Tendsto (fun p : G × G => p.1⁻¹ * p.2) (𝓝 (g, g)) (𝓝 1) := by
    simpa only [inv_mul_cancel] using hc.tendsto (g, g)
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp (ht.eventually hU)
  obtain ⟨K, hKg, hKsub, hKc⟩ := local_compact_nhds (inter_mem hV hW)
  refine ⟨K, hKc, hKg, ?_⟩
  intro a ha b hb
  exact hVW (show (a, b) ∈ V ×ˢ W from ⟨(hKsub ha).1, (hKsub hb).2⟩)

/-- Poincaré recurrence in the topology of orbit parameters. This does not
require the orbit image to be closed or its inverse parametrization continuous. -/
theorem exists_close_parameters_of_orbit_recurrence
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    (f : X → X) (hf : MeasurePreserving f μ μ)
    (ψ : G → X) (hψ : Continuous ψ) (hfull : ∀ᵐ x ∂μ, x ∈ range ψ)
    (U : Set G) (hU : U ∈ 𝓝 1) (N : ℕ) :
    ∃ n > N, ∃ a b : G, a⁻¹ * b ∈ U ∧ f^[n] (ψ a) = ψ b := by
  choose K hKc hKg hKsmall using exists_compact_close_parameter_neighborhood U hU
  obtain ⟨t, ht, hcover⟩ := countable_cover_nhds hKg
  have hpos : ∃ g ∈ t, μ (ψ '' K g) ≠ 0 := by
    by_contra hnone
    have hz : ∀ g ∈ t, μ (ψ '' K g) = 0 := by simpa only [not_exists, not_and, not_not] using hnone
    have hnot : ∀ᵐ x ∂μ, ∀ g ∈ t, x ∉ ψ '' K g := by
      apply (ae_ball_iff ht).mpr
      intro g hg
      exact measure_eq_zero_iff_ae_notMem.mp (hz g hg)
    obtain ⟨x, hx, hn⟩ := (hfull.and hnot).exists
    obtain ⟨a, rfl⟩ := hx
    have ha : a ∈ ⋃ g ∈ t, K g := by rw [hcover]; trivial
    obtain ⟨g, hg, haK⟩ := mem_iUnion₂.mp ha
    exact hn g hg ⟨a, haK, rfl⟩
  obtain ⟨g, _, hg⟩ := hpos
  have hmeas : MeasurableSet (ψ '' K g) := ((hKc g).image hψ).isClosed.measurableSet
  obtain ⟨n, hn, hret⟩ := hf.conservative.exists_gt_measure_inter_ne_zero hmeas.nullMeasurableSet hg N
  obtain ⟨x, hx, hfx⟩ := nonempty_of_measure_ne_zero hret
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hbeq⟩ := hfx
  exact ⟨n, hn, a, b, hKsmall g a ha b hb, hbeq.symm⟩

end DukePrimeDegree

end

end OAI
