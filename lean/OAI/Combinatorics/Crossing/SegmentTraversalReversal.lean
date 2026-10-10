import OAI.Combinatorics.Crossing.PolygonalChainTransversality
import OAI.Combinatorics.Crossing.SegmentClosedIncidence

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segmentPairTransverse_of_not_meet (a b c d : Plane) (h : ¬ ClosedSegmentsMeet a b c d) :
    SegmentPairTransverse a b c d := by
  intro s hs t ht he
  exact False.elim (h ⟨s,hs,t,ht,he⟩)

theorem segmentCrossingSign_eq_zero_of_not_meet (a b c d : Plane) (h : ¬ ClosedSegmentsMeet a b c d) :
    segmentCrossingSign a b c d=0 := by
  have hn : ¬ SegmentsCrossProperly a b c d := fun hh => h (closedSegmentsMeet_of_proper _ _ _ _ hh)
  simp [segmentCrossingSign,hn]

theorem segmentPairTransverse_reverse_left (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    SegmentPairTransverse b a c d := by
  intro s hs t ht he
  have hs' : 1-s ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have he' : segmentPoint a b (1-s)=segmentPoint c d t := (segmentPoint_reverse b a s).trans he
  obtain ⟨hdet,hsp,htp⟩ := h (1-s) hs' t ht he'
  refine ⟨?_,⟨by linarith [hsp.2],by linarith [hsp.1]⟩,htp⟩
  have hab : a-b=-(b-a) := by abel
  rw [hab,det2_neg_left]
  exact neg_ne_zero.mpr hdet

theorem segmentPairTransverse_reverse_right (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    SegmentPairTransverse a b d c :=
  segmentPairTransverse_swap _ _ _ _
    (segmentPairTransverse_reverse_left _ _ _ _ (segmentPairTransverse_swap _ _ _ _ h))

namespace PolygonalChain
variable {O T : Set Plane} {a b c d : Plane}

theorem transverse_reverse_left (P : PolygonalChain O a b) (Q : PolygonalChain T c d)
    (h : P.Transverse Q) : P.reverse.Transverse Q := by
  intro i j
  have hi : i.val<P.pieces := i.isLt
  have h₀ : P.pieces-i.val=P.pieces-1-i.val+1 := by omega
  have h₁ : P.pieces-(i.val+1)=P.pieces-1-i.val := by omega
  change SegmentPairTransverse (P.vertices (P.pieces-i.val)) (P.vertices (P.pieces-(i.val+1))) _ _
  rw [h₀,h₁]
  exact segmentPairTransverse_reverse_left _ _ _ _ (h ⟨P.pieces-1-i.val,by omega⟩ j)

theorem transverse_reverse_right (P : PolygonalChain O a b) (Q : PolygonalChain T c d)
    (h : P.Transverse Q) : P.Transverse Q.reverse :=
  Q.reverse.transverse_swap P (Q.transverse_reverse_left P (P.transverse_swap Q h))

end PolygonalChain
end Zarankiewicz

end

end OAI
