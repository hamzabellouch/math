import OAI.Analysis.KadisonKastler.PublishedBoundary
import OAI.Analysis.KadisonKastler.StandardFiniteIsomorphism
import OAI.Analysis.KadisonKastler.CountableTraceGroup

namespace OAI

/-! # Common-position isomorphism from the published scalar inputs

The countable group is constructed from trace-dense unitaries. The
boundary, both scalar means, and double ergodicity are then supplied by
`PublishedBoundary`. The only additional input is the family of constant-
field specializations of Tomiyama's Theorem 1(2), Proceedings of the Japan
Academy 33 (1957), 608--612, pp. 608--609.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- Tomiyama's same published theorem, specialized to every scalar field
base and group used on the fixed represented Hilbert space. -/
def PublishedFieldTomiyamaFamily : Prop :=
  ∀ (G D : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [MeasurableSpace D] (μ : Measure D) [IsFiniteMeasure μ],
    PublishedFieldTomiyama (G := G) (H := H) (μ := μ)

variable {H} {M N : VonNeumannAlgebra H}

/-- Published scalar hypotheses determine the group and boundary data
for the standard-position theorem. -/
theorem exists_standard_finiteFactor_isomorphism_of_published
    (hBoundary : PublishedBoundary.{u}) (hTom : PublishedFieldTomiyamaFamily H)
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (pM : StandardTracialPosition M) (pN : StandardTracialPosition N)
    (hΩ : pM.vector = pN.vector)
    {b : ℝ} (hb : b < 1 / 100000) (hgap : kkDistance M N < b)
    (hJ : ‖(pM.conjugation : H →L⋆[ℂ] H) -
      (pN.conjugation : H →L⋆[ℂ] H)‖ ≤ 768 * b) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      ∀ x, ‖(θ x : H →L[ℂ] H) - (x : H →L[ℂ] H)‖ ≤ 378 * b * ‖x‖ := by
  classical
  obtain ⟨G, hGc, hGdense⟩ :=
    exists_countable_traceDense_unitary_subgroup pM.trace pM.finiteVectorTrace
  let : Countable G := hGc.to_subtype
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := discreteTopology_bot G
  obtain ⟨D, hD, μ, hμ, α, hm, hm₂, herg⟩ := hBoundary G
  let : MeasurableSpace D := hD
  let : IsProbabilityMeasure μ := hμ
  obtain ⟨m⟩ := hm
  obtain ⟨m₂⟩ := hm₂
  exact exists_standard_finiteFactor_isomorphism hM hN pM pN hΩ α m m₂
    (hTom G D μ) (hTom (G × G) (D × D) (μ.prod μ)) herg G.subtype hGdense hb hgap hJ

end

end KadisonKastler

end OAI
