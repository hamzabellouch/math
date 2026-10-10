import OAI.NumberTheory.DukePrimeDegree.Dynamics.CompactFlowReturns
import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafLusin

namespace OAI

/-!
# Simultaneous returns to compact Lusin sets

The compact recurrence construction retains continuity of a measurable
observable. This supplies one conull set for all pairs in the pointwise
stable-holonomy argument.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace DukePrimeDegree

theorem exists_conull_lusin_flow_returns
    {Y Z : Type*} [TopologicalSpace Y] [MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Y) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    (F : Y → Z) (hF : Measurable F)
    (N : Set Y) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    ∃ M : Set Y, MeasurableSet M ∧ μ M = 0 ∧
      ∀ x ∉ M, ∀ y ∉ M, ∃ K : Set Y, IsCompact K ∧ K ⊆ Nᶜ ∧ ContinuousOn F K ∧
        ∀ R : ℝ, ∃ t : ℝ, R < t ∧ Φ t x ∈ K ∧ Φ t y ∈ K := by
  have hK (m : ℕ) := exists_compact_continuousOn_metrizable μ F hF N hN hNzero
    (ENNReal.ofReal (((1 / 2 : ℝ) ^ m) / 8))
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  choose K hcompact hKN hsmall hcont using hK
  obtain ⟨G, hGmeas, hae, hgood⟩ := exists_eventual_flow_good_sets μ hΦ hzero hadd hpres
    K (fun m => (hcompact m).isClosed.measurableSet) hsmall
  obtain ⟨M, hbad, hM, hMzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  refine ⟨M, hM, hMzero, ?_⟩
  intro x hx y hy
  have hxG : ∀ᶠ m in atTop, x ∈ G m := by
    by_contra h
    exact hx (hbad h)
  have hyG : ∀ᶠ m in atTop, y ∈ G m := by
    by_contra h
    exact hy (hbad h)
  obtain ⟨m, hxm, hym⟩ := (hxG.and hyG).exists
  exact ⟨K m, hcompact m, hKN m, hcont m,
    exists_late_simultaneous_compact_return Φ (K m) x y
      (hgood m x hxm) (hgood m y hym)⟩

end DukePrimeDegree

end

end OAI
