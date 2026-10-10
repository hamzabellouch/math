import OAI.Combinatorics.Crossing.CircleOffsetParameter
import OAI.Combinatorics.Crossing.GeneralSpokeAveraging
import OAI.Combinatorics.Crossing.FiniteScaledRadius

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_physical_spoke_average (node scale : ι → ℝ) (hn : Function.Injective node)
    (hs : ∀ i, scale i ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ a b c d : ι, a ≠ b → c ≠ d →
      (segmentCrossingSign (circlePoint (node a)) (circlePoint (node b))
          (circleOffset (circlePoint (node c)) (scale c*t))
          (circleOffset (circlePoint (node d)) (scale d*t)) +
        segmentCrossingSign (circlePoint (node a)) (circlePoint (node b))
          (circleOffset (circlePoint (node c)) (scale c*(-t)))
          (circleOffset (circlePoint (node d)) (scale d*(-t)))) / 2 =
        chordEndpointPairing (node a) (node b) (node c) (node d) := by
  obtain ⟨γ,hγ,hgap⟩ := finite_node_separation node hn
  let ε := γ/3
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsep (i j : ι) (hij : i ≠ j) : 2*ε < |node i-node j| := by
    have hh := hgap i j hij
    dsimp [ε]
    linarith
  have hex (i : ι) := exists_circle_offset_parameter_radius (node i) ε hε
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_scaled_radius scale radius hpos
  refine ⟨δ,hδ,?_⟩
  intro t ht htδ a b c d hab hcd
  have hbt : |t| < δ := by simpa [abs_of_pos ht] using htδ
  have hbmt : |-t| < δ := by simpa [abs_neg] using hbt
  let plus : ι → ℝ := fun i => offsetParameter (node i) (scale i*t)
  let minus : ι → ℝ := fun i => offsetParameter (node i) (scale i*(-t))
  have hp (i : ι) := hprop i (scale i*t) (hbound t hbt i)
  have hm (i : ι) := hprop i (scale i*(-t)) (hbound (-t) hbmt i)
  have hpnear (i : ι) : |plus i-node i| < ε := (hp i).2.1
  have hmnear (i : ι) : |minus i-node i| < ε := (hm i).2.1
  have hstraddle (i : ι) : (plus i<node i ∧ node i<minus i) ∨
      (minus i<node i ∧ node i<plus i) := by
    have hne : scale i*t ≠ 0 := mul_ne_zero (hs i) (ne_of_gt ht)
    rcases lt_or_gt_of_ne hne with hi | hi
    · exact Or.inl ⟨(hp i).2.2.2 hi,(hm i).2.2.1 (by nlinarith)⟩
    · exact Or.inr ⟨(hm i).2.2.2 (by nlinarith),(hp i).2.2.1 hi⟩
  have havg := local_spoke_straddling_average node plus minus hn ε hε hsep hpnear hmnear hstraddle a b c d hab hcd
  have hpe (i : ι) : circlePoint (plus i)=circleOffset (circlePoint (node i)) (scale i*t) := (hp i).1
  have hme (i : ι) : circlePoint (minus i)=circleOffset (circlePoint (node i)) (scale i*(-t)) := (hm i).1
  simpa only [hpe,hme] using havg

end Zarankiewicz

end

end OAI
