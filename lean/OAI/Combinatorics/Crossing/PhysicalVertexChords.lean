import OAI.Combinatorics.Crossing.UniformSpokeRadii
import OAI.Combinatorics.Crossing.RoundCircleChords
import OAI.Combinatorics.Crossing.DiskSegments

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem shifted_chords_transverse (j : BipartiteVertex m n) (a b c d : IncidentEdges j)
    (ε : ℝ) (hsmall : ∀ e : IncidentEdges j, |V.spokeScale j e*ε|≤1)
    (hsep : ∀ e f : IncidentEdges j, V.spokePort j e ≠ C.shiftedPort j f ε)
    (hinj : Function.Injective (fun e : IncidentEdges j => C.shiftedPort j e ε))
    (hab : a ≠ b) (hcd : c ≠ d) :
    SegmentPairTransverse (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c ε) (C.shiftedPort j d ε) :=
  round_circle_chords_transverse (D.vertex j) _ _ _ _ V.radius
    (V.spokePort_circle j a) (V.spokePort_circle j b)
    (C.shiftedPort_circle j c ε (hsmall c)) (C.shiftedPort_circle j d ε (hsmall d))
    ((C.port_injective j).ne hab) (hinj.ne hcd) (hsep a c) (hsep a d) (hsep b c) (hsep b d)

theorem chord_connector_disjoint (j : BipartiteVertex m n) (a b e : IncidentEdges j)
    (ε : ℝ) (hne : ε ≠ 0) (hsmall : |V.spokeScale j e*ε|<1) (hab : a ≠ b)
    (ha : V.spokePort j a ≠ C.shiftedPort j e ε) (hb : V.spokePort j b ≠ C.shiftedPort j e ε) :
    ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j e ε) (C.tangentPort j e ε) := by
  have hunit (f : IncidentEdges j) : squaredLength (circlePoint (C.node j f))=1 := circlePoint_on_unit_circle _
  have haq : circlePoint (C.node j a) ≠ circleOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε) := by
    intro he
    apply ha
    rw [← C.point_eq j a]
    exact congrArg (similarityPoint (D.vertex j) (C.frame j)) he
  have hbq : circlePoint (C.node j b) ≠ circleOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε) := by
    intro he
    apply hb
    rw [← C.point_eq j b]
    exact congrArg (similarityPoint (D.vertex j) (C.frame j)) he
  have hd := unit_chord_connector_disjoint (circlePoint (C.node j a)) (circlePoint (C.node j b))
    (circlePoint (C.node j e)) (hunit a) (hunit b) (hunit e)
    (fun he => hab (C.node_injective j (circlePoint_injective he)))
    (V.spokeScale j e*ε) hsmall (mul_ne_zero (V.spokeScale_ne_zero j e) hne) haq hbq
  rintro ⟨s,hs,t,ht,he⟩
  apply hd
  refine ⟨s,hs,t,ht,?_⟩
  apply similarityPoint_injective (D.vertex j) (C.frame j) (C.frame_ne_zero j)
  simpa only [similarityPoint_segment,C.point_eq,← C.tangentPort_eq,shiftedPort] using he

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
