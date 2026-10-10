import OAI.Combinatorics.Crossing.TruncatedRadialDots

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

theorem shifted_first_piece_exterior (e : BipartiteEdge m n) (ε ℓ : ℝ)
    (hε : ε ≠ 0) (hℓ : 0<ℓ)
    (hdir : shiftedTrack (V.vertices e) (V.pieces e) ε 1-
      shiftedTrack (V.vertices e) (V.pieces e) ε 0=ℓ • trackDirection (V.vertices e) 0) :
    segment ℝ (shiftedTrack (V.vertices e) (V.pieces e) ε 0)
      (shiftedTrack (V.vertices e) (V.pieces e) ε 1) ⊆
      {x | V.radius^2 < squaredLength (x-D.vertex (Sum.inl e.1))} := by
  have hstart : shiftedTrack (V.vertices e) (V.pieces e) ε 0=
      V.startPort e+ε • normalShift (trackDirection (V.vertices e) 0) := by
    simp [shiftedTrack,trackOffset,V.vertices_first]
  have hc : squaredLength (V.startPort e-D.vertex (Sum.inl e.1))=V.radius^2 := by
    simpa only [V.spokePort_left] using V.spokePort_circle (Sum.inl e.1) (V.leftIncident e)
  have hp : det2 (trackDirection (V.vertices e) 0) (V.startPort e-D.vertex (Sum.inl e.1))=0 := by
    simpa [spokeDirection,spokeIndex,leftIncident,spokePort,drawingSpokePort,startPort] using
      V.spokeDirection_parallel (Sum.inl e.1) (V.leftIncident e)
  rw [hstart] at hdir ⊢
  exact normal_offset_segment_exterior _ _ _ _ _ ε ℓ (V.direction_ne_zero e 0 (V.pieces_pos e))
    hc hp (mul_nonneg hℓ.le (V.start_radial_dot_pos e).le) hε hdir

theorem shifted_last_piece_exterior (e : BipartiteEdge m n) (ε ℓ : ℝ)
    (hε : ε ≠ 0) (hℓ : 0<ℓ)
    (hdir : shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)-
      shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e-1)=
        ℓ • trackDirection (V.vertices e) (V.pieces e-1)) :
    segment ℝ (shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e-1))
      (shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)) ⊆
      {x | V.radius^2 < squaredLength (x-D.vertex (Sum.inr e.2))} := by
  have hn : V.pieces e ≠ 0 := ne_of_gt (V.pieces_pos e)
  have hi : V.pieces e-1 < V.pieces e := by have hh := V.pieces_pos e; omega
  have hend : shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)=
      V.endPort e+ε • normalShift (trackDirection (V.vertices e) (V.pieces e-1)) := by
    simp [shiftedTrack,trackOffset,hn,V.vertices_last]
  have hc : squaredLength (V.endPort e-D.vertex (Sum.inr e.2))=V.radius^2 := by
    simpa only [V.spokePort_right] using V.spokePort_circle (Sum.inr e.2) (V.rightIncident e)
  have hp : det2 (trackDirection (V.vertices e) (V.pieces e-1)) (V.endPort e-D.vertex (Sum.inr e.2))=0 := by
    simpa [spokeDirection,spokeIndex,rightIncident,spokePort,drawingSpokePort,endPort] using
      V.spokeDirection_parallel (Sum.inr e.2) (V.rightIncident e)
  have hrev : shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e-1)-
      (V.endPort e+ε • normalShift (trackDirection (V.vertices e) (V.pieces e-1)))=
        (-ℓ) • trackDirection (V.vertices e) (V.pieces e-1) := by
    rw [neg_smul,← hdir,hend]
    abel
  rw [segment_symm,hend]
  exact normal_offset_segment_exterior _ _ _ _ _ ε (-ℓ) (V.direction_ne_zero e _ hi)
    hc hp (mul_nonneg_of_nonpos_of_nonpos (by linarith) (V.end_radial_dot_neg e).le) hε hrev

end Zarankiewicz.VertexTruncation

end

end OAI
