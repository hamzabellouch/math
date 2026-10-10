import OAI.Combinatorics.Crossing.TruncatedSpokeCoordinates
import OAI.Combinatorics.Crossing.FiniteMovingPoints

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem continuous_shiftedPort (j : BipartiteVertex m n) (e : IncidentEdges j) :
    Continuous (C.shiftedPort j e) := by
  change Continuous (fun ε : ℝ => similarityPoint (D.vertex j) (C.frame j)
    (circleOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε)))
  dsimp [similarityPoint,circleOffset,rotateQuarter]
  fun_prop

theorem shiftedPort_zero (j : BipartiteVertex m n) (e : IncidentEdges j) :
    C.shiftedPort j e 0=V.spokePort j e := by
  simp only [shiftedPort,mul_zero,circleOffset_zero,C.point_eq]

theorem shiftedPort_ne_original (j : BipartiteVertex m n) (e : IncidentEdges j)
    (ε : ℝ) (hε : ε ≠ 0) : C.shiftedPort j e ε ≠ V.spokePort j e := by
  intro he
  have hh := C.shiftedPort_level j e ε
  rw [he,sub_self] at hh
  have hz : det2 (V.spokeDirection j e) (0 : Plane)=0 := by simp [det2]
  rw [hz] at hh
  exact hε hh.symm

theorem exists_endpoint_separation_radius (j : BipartiteVertex m n) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ →
      (∀ e f : IncidentEdges j, V.spokePort j e ≠ C.shiftedPort j f ε) ∧
      Function.Injective (fun e : IncidentEdges j => C.shiftedPort j e ε) := by
  have hinj : Function.Injective (fun e : IncidentEdges j => C.shiftedPort j e 0) := by
    intro e f he
    have hh : circlePoint (C.node j e)=circlePoint (C.node j f) := by
      apply similarityPoint_injective (D.vertex j) (C.frame j) (C.frame_ne_zero j)
      simpa only [shiftedPort,mul_zero,circleOffset_zero] using he
    exact C.node_injective j (circlePoint_injective hh)
  obtain ⟨δ,hδ,hh⟩ := finite_moving_points_separation (C.shiftedPort j)
    (C.continuous_shiftedPort j) hinj
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall
  constructor
  · intro e f
    by_cases hef : e=f
    · subst f
      exact (C.shiftedPort_ne_original j e ε hε).symm
    · simpa only [C.shiftedPort_zero] using (hh ε hsmall e f hef).1
  · intro e f he
    by_contra hef
    exact (hh ε hsmall e f hef).2 he

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
