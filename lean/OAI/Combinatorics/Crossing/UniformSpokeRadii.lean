import OAI.Combinatorics.Crossing.SpokeEndpointSeparation
import OAI.Combinatorics.Crossing.FiniteScaledRadius

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem port_injective (C : TruncatedSpokeCoordinates V) (j : BipartiteVertex m n) : Function.Injective (V.spokePort j) := by
  intro e f he
  apply C.node_injective j
  apply circlePoint_injective
  apply similarityPoint_injective (D.vertex j) (C.frame j) (C.frame_ne_zero j)
  simpa only [C.point_eq] using he

theorem exists_uniform_endpoint_radius :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j : BipartiteVertex m n,
      (∀ e f : IncidentEdges j, V.spokePort j e ≠ C.shiftedPort j f ε) ∧
      Function.Injective (fun e : IncidentEdges j => C.shiftedPort j e ε) := by
  classical
  choose radius hpos hprop using C.exists_endpoint_separation_radius
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun j _ => hpos j)
  exact ⟨δ,hδ,fun ε hε hsmall j => hprop j ε hε (hsmall.trans (hbound j (Finset.mem_univ _)))⟩

theorem exists_uniform_scale_radius (_C : TruncatedSpokeCoordinates V) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j (e : IncidentEdges j), |V.spokeScale j e*ε|<1 := by
  let Spoke := Σ j : BipartiteVertex m n, IncidentEdges j
  obtain ⟨δ,hδ,hbound⟩ := finite_scaled_radius
    (fun s : Spoke => V.spokeScale s.1 s.2) (fun _ => (1 : ℝ)) (by intro s; norm_num)
  exact ⟨δ,hδ,fun ε hε j e => hbound ε hε ⟨j,e⟩⟩

theorem exists_uniform_average_radius :
    ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, 0<t → t<δ → ∀ j (a b c d : IncidentEdges j),
      a ≠ b → c ≠ d →
      (segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c t) (C.shiftedPort j d t)+
        segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c (-t)) (C.shiftedPort j d (-t)))/2 =
      chordEndpointPairing (C.node j a) (C.node j b) (C.node j c) (C.node j d) := by
  classical
  choose radius hpos hprop using C.exists_vertex_average_radius
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun j _ => hpos j)
  exact ⟨δ,hδ,fun t ht hsmall j => hprop j t ht (hsmall.trans (hbound j (Finset.mem_univ _)))⟩

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
