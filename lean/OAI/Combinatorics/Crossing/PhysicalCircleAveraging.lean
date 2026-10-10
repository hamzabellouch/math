import OAI.Combinatorics.Crossing.FiniteCircleCoordinates
import OAI.Combinatorics.Crossing.PhysicalSpokeAveraging

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem physical_spoke_average_in_similarity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o u : Plane) (hu : u ≠ 0) (node scale : ι → ℝ)
    (hn : Function.Injective node) (hs : ∀ i, scale i ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ a b c d : ι, a ≠ b → c ≠ d →
      (segmentCrossingSign
          (similarityPoint o u (circlePoint (node a))) (similarityPoint o u (circlePoint (node b)))
          (similarityPoint o u (circleOffset (circlePoint (node c)) (scale c*t)))
          (similarityPoint o u (circleOffset (circlePoint (node d)) (scale d*t))) +
        segmentCrossingSign
          (similarityPoint o u (circlePoint (node a))) (similarityPoint o u (circlePoint (node b)))
          (similarityPoint o u (circleOffset (circlePoint (node c)) (scale c*(-t))))
          (similarityPoint o u (circleOffset (circlePoint (node d)) (scale d*(-t))))) / 2 =
        chordEndpointPairing (node a) (node b) (node c) (node d) := by
  obtain ⟨δ,hδ,hh⟩ := exists_physical_spoke_average node scale hn hs
  refine ⟨δ,hδ,?_⟩
  intro t ht hsmall a b c d hab hcd
  simpa only [segmentCrossingSign_similarity o u _ _ _ _ hu] using hh t ht hsmall a b c d hab hcd

theorem actual_circle_spoke_averaging {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : Plane) (r : ℝ) (hr : 0 < r) (point : ι → Plane)
    (hinj : Function.Injective point) (hcircle : ∀ i, squaredLength (point i-o)=r^2)
    (scale : ι → ℝ) (hs : ∀ i, scale i ≠ 0) :
    ∃ u : Plane, u ≠ 0 ∧ squaredLength u=r^2 ∧
      ∃ node : ι → ℝ, Function.Injective node ∧
        (∀ i, similarityPoint o u (circlePoint (node i))=point i) ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ a b c d : ι, a ≠ b → c ≠ d →
          (segmentCrossingSign (point a) (point b)
              (similarityPoint o u (circleOffset (circlePoint (node c)) (scale c*t)))
              (similarityPoint o u (circleOffset (circlePoint (node d)) (scale d*t))) +
            segmentCrossingSign (point a) (point b)
              (similarityPoint o u (circleOffset (circlePoint (node c)) (scale c*(-t))))
              (similarityPoint o u (circleOffset (circlePoint (node d)) (scale d*(-t))))) / 2 =
            chordEndpointPairing (node a) (node b) (node c) (node d) := by
  obtain ⟨u,hu,hlen,node,hn,hnode⟩ := exists_finite_circle_coordinates o r hr point hinj hcircle
  obtain ⟨δ,hδ,hh⟩ := physical_spoke_average_in_similarity o u hu node scale hn hs
  refine ⟨u,hu,hlen,node,hn,hnode,δ,hδ,?_⟩
  intro t ht hsmall a b c d hab hcd
  simpa only [hnode] using hh t ht hsmall a b c d hab hcd

end Zarankiewicz

end

end OAI
