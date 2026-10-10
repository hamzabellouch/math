import OAI.Combinatorics.Crossing.TrackEndpointConnections
import OAI.Combinatorics.Crossing.NormalOffsetExterior

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem dot2_scaled_self (v : Plane) (a b : ℝ) : dot2 (a • v) (b • v)=a*b*squaredLength v := by
  dsimp [dot2,squaredLength]
  ring

namespace VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

theorem start_radial_dot_pos (e : BipartiteEdge m n) :
    0 < dot2 (V.startPort e-D.vertex (Sum.inl e.1)) (trackDirection (V.vertices e) 0) := by
  have hp := V.pieces_pos e
  have hα := (radialPort_parameter_half ((V.chain e).vertices 0) ((V.chain e).vertices 1)
    V.radius V.radius_pos (V.short e).1).1
  have hβ := (V.chain e).truncatedScale_pos V.radius V.radius_pos (V.short e).1 (V.short e).2 0
  have he : V.startPort e-D.vertex (Sum.inl e.1)=
      (V.chain e).startFraction V.radius • trackDirection (V.chain e).vertices 0 := by
    have hh := radialPort_sub ((V.chain e).vertices 0) ((V.chain e).vertices 1) V.radius
    change (V.chain e).startPort V.radius-(V.chain e).vertices 0=
      (V.chain e).startFraction V.radius • trackDirection (V.chain e).vertices 0 at hh
    simpa only [startPort,(V.chain e).first] using hh
  rw [he]
  change 0 < dot2 _ (trackDirection ((V.chain e).truncatedVertices V.radius) 0)
  rw [(V.chain e).truncated_direction V.radius 0 hp,dot2_scaled_self]
  exact mul_pos (mul_pos hα hβ)
    (squaredLength_pos _ ((V.chain e).minimum_piece_ne_zero (V.minimal e) 0 hp))

theorem end_radial_dot_neg (e : BipartiteEdge m n) :
    dot2 (V.endPort e-D.vertex (Sum.inr e.2))
      (trackDirection (V.vertices e) (V.pieces e-1)) < 0 := by
  have hp := V.pieces_pos e
  have hp' : 0 < (V.chain e).pieces := hp
  have hi : V.pieces e-1 < V.pieces e := by omega
  have hα := (radialPort_parameter_half ((V.chain e).vertices ((V.chain e).pieces-1))
    ((V.chain e).vertices (V.chain e).pieces) V.radius V.radius_pos (V.short e).2).1
  have hβ := (V.chain e).truncatedScale_pos V.radius V.radius_pos (V.short e).1 (V.short e).2 (V.pieces e-1)
  have he : V.endPort e-D.vertex (Sum.inr e.2)=
      (-(V.chain e).endFraction V.radius) • trackDirection (V.chain e).vertices (V.pieces e-1) := by
    have hh : (V.chain e).endPort V.radius-(V.chain e).vertices (V.chain e).pieces=
        (-(V.chain e).endFraction V.radius) • trackDirection (V.chain e).vertices (V.pieces e-1) := by
      rw [(V.chain e).endPort_eq_fraction]
      simp only [trackDirection,pieces,show (V.chain e).pieces-1+1=(V.chain e).pieces by omega,neg_smul]
      abel
    simpa only [endPort,(V.chain e).last] using hh
  rw [he]
  change dot2 _ (trackDirection ((V.chain e).truncatedVertices V.radius) (V.pieces e-1)) < 0
  rw [(V.chain e).truncated_direction V.radius _ hi,dot2_scaled_self]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hα) hβ)
    (squaredLength_pos _ ((V.chain e).minimum_piece_ne_zero (V.minimal e) _ hi))

theorem bend_ne_zero (e : BipartiteEdge m n) (i : ℕ) (hi0 : 0 < i) (hin : i < V.pieces e) :
    det2 (trackDirection (V.vertices e) (i-1)) (trackDirection (V.vertices e) i) ≠ 0 := by
  exact (V.chain e).truncated_bend_ne_zero (V.minimal e) V.radius V.radius_pos
    (V.short e).1 (V.short e).2 i hi0 hin

theorem exists_forward_radius (e : BipartiteEdge m n) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ i : Fin (V.pieces e),
      ∃ ℓ : ℝ, 0<ℓ ∧ shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1)-
        shiftedTrack (V.vertices e) (V.pieces e) ε i.val=ℓ • trackDirection (V.vertices e) i.val :=
  exists_forward_shiftedTrack_radius (V.vertices e) (V.pieces e) (V.direction_ne_zero e) (V.bend_ne_zero e)

end VertexTruncation
end Zarankiewicz

end

end OAI
