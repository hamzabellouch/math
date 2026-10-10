import OAI.Combinatorics.Crossing.DrawingSpokePorts

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem radialPort_parameter_half (a b : Plane) (r : ℝ) (hr : 0 < r)
    (hshort : 4*r^2 < squaredLength (b-a)) :
    0 < r/Real.sqrt (squaredLength (b-a)) ∧ r/Real.sqrt (squaredLength (b-a)) < 1/2 := by
  have hL : 0 < squaredLength (b-a) := by nlinarith [sq_nonneg r]
  have hs := Real.sqrt_pos.mpr hL
  have hs2 := Real.sq_sqrt hL.le
  exact ⟨div_pos hr hs,(div_lt_iff₀ hs).mpr (by nlinarith)⟩

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

def startFraction (P : PolygonalChain O a b) (r : ℝ) : ℝ :=
  r/Real.sqrt (squaredLength (P.vertices 1-P.vertices 0))

def endFraction (P : PolygonalChain O a b) (r : ℝ) : ℝ :=
  r/Real.sqrt (squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)))

def truncatedVertices (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) : Plane :=
  if i=0 then P.startPort r else if i=P.pieces then P.endPort r else P.vertices i

theorem startPort_eq_fraction (P : PolygonalChain O a b) (r : ℝ) :
    P.startPort r=P.vertices 0+P.startFraction r • (P.vertices 1-P.vertices 0) := rfl

theorem endPort_eq_fraction (P : PolygonalChain O a b) (r : ℝ) :
    P.endPort r=P.vertices P.pieces-P.endFraction r • (P.vertices P.pieces-P.vertices (P.pieces-1)) := by
  unfold endPort radialPort endFraction
  rw [squaredLength_sub_comm (P.vertices (P.pieces-1)) (P.vertices P.pieces)]
  apply Prod.ext <;> dsimp <;> ring

theorem truncatedVertices_first (P : PolygonalChain O a b) (r : ℝ) :
    P.truncatedVertices r 0=P.startPort r := by simp [truncatedVertices]

theorem truncatedVertices_last (P : PolygonalChain O a b) (hp : 0 < P.pieces) (r : ℝ) :
    P.truncatedVertices r P.pieces=P.endPort r := by simp [truncatedVertices,ne_of_gt hp]

theorem truncated_piece_subset (P : PolygonalChain O a b) (r : ℝ) (hr : 0 < r)
    (hfirst : r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)))
    (i : ℕ) (hi : i < P.pieces) :
    segment ℝ (P.truncatedVertices r i) (P.truncatedVertices r (i+1)) ⊆
      segment ℝ (P.vertices i) (P.vertices (i+1)) := by
  apply (convex_segment (𝕜 := ℝ) _ _).segment_subset
  · by_cases h0 : i=0
    · subst i
      rw [truncatedVertices_first]
      exact openSegmentTrace_subset_segment _ _ (radialPort_mem_openSegment _ _ r hr hfirst)
    · simp only [truncatedVertices,ite_eq_right h0,ite_eq_right (show i ≠ P.pieces by omega)]
      exact left_mem_segment ℝ _ _
  · by_cases hn : i+1=P.pieces
    · rw [show P.truncatedVertices r (i+1)=P.endPort r by rw [hn]; exact P.truncatedVertices_last (by omega) r]
      have hh : i=P.pieces-1 := by omega
      have hs : r^2 < squaredLength (P.vertices (P.pieces-1)-P.vertices P.pieces) := by
        rwa [squaredLength_sub_comm]
      have hx := openSegmentTrace_reverse_mem _ _ _ (radialPort_mem_openSegment _ _ r hr hs)
      have hseg := openSegmentTrace_subset_segment _ _ hx
      simpa only [endPort,hh,show P.pieces-1+1=P.pieces by omega] using hseg
    · simp only [truncatedVertices,ite_eq_right (show i+1 ≠ 0 by omega),ite_eq_right hn]
      exact right_mem_segment ℝ _ _

end PolygonalChain
end Zarankiewicz

end

end OAI
