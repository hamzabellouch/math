import OAI.Combinatorics.SphericalRamsey.Specification

namespace OAI

namespace GrahamSpherical

/-- Fixed fifty-color avoidance in every positive dimension contradicts the
ordinary Ramsey quantifier, without assuming any copy exists. -/
theorem not_euclideanRamsey_of_fifty_colorings
    (havoid : ∀ n : ℕ, 0 < n →
      ∃ color : Point n → Fin 50, AvoidsCopy witness color) :
    ¬ EuclideanRamsey witness := by
  intro hRamsey
  obtain ⟨n, hn, hall⟩ := hRamsey 50 (by decide)
  obtain ⟨color, hc⟩ := havoid n hn
  exact hc (hall color)

/-- The geometric and coloring properties jointly imply the spherical
non-Ramsey conclusion. -/
theorem assemble_full_result
    (hcard : witness.ncard = 12)
    (hsphere : witness ⊆ Metric.sphere (0 : Point 2) 1)
    (havoid : ∀ n : ℕ, 0 < n →
      ∃ color : Point n → Fin 50, AvoidsCopy witness color) :
    Specification.FullAuthoredResult :=
  ⟨hcard, hsphere, havoid, not_euclideanRamsey_of_fifty_colorings havoid⟩

end GrahamSpherical

end OAI
