import OAI.Geometry.Convex.GeneralMahler.Segment.Positive
import OAI.Geometry.Convex.GeneralMahler.Middle.Tiles

namespace OAI
open Set Filter MeasureTheory Real
namespace GeneralMahler.SCal
open Profile Grid Jet Mid SE Segment

theorem Eq04full (h:NG)(C:PrefixC)(hW:Works C)(hG:Good C) :
    SegmentOK := by
  intro x y ha
  obtain ⟨l,hx⟩:=ontoX x
  obtain ⟨r,hy⟩:=ontoX y
  have hl:l<r:= x_mono.lt_iff_lt.mp (by rwa [hx,hy])
  let m:=(l+r)/2
  let k:=(r-l)/2
  have hk:0<k:=by unfold k;linarith
  have he:(x,y)= seg m k:= by
    unfold seg left right m k
    rw [show (l+r)/2-(r-l)/2=l by ring, show (l+r)/2+(r-l)/2=r by ring,hx,hy]
  rw [he]
  have he(m:ℝ)(hp:0 ≤ m):symR (seg m k)<0:=by
    let a:=left m k;let b:=right m k
    have hs : b-a=2*k:=by unfold b a left right;ring
    rcases le_total k (16/100) with hg|hg
    · exact short h m hk hg
    have hi : |a|≤b:= by unfold a b left right; rw [abs_le];constructor<;>linarith
    by_cases ha:a ≤ -(14/10)
    · apply reduce_f m (hSeg01 h) hk (sCase2 h m k hp ha)
    by_cases hb: 14/10 ≤ a
    · apply reduce_f m (hSeg01 h) hk (costPos h m k hb hg)
    have hx : |a| ≤ 14/10:=by rw [abs_le];constructor<;> linarith
    rcases le_total b (36/10) with hf|hf
    · exact has_middle C h hW hG a b hx hf hi (by linarith)
    apply reduce_f m (hSeg01 h) hk (sCase1 h m k hx hf)
  rcases le_total 0 m with hh|hh
  · exact he m hh
  rw [← cost_ref _ (hSeg01 h),neg_left]
  apply he _ (by linarith)
end GeneralMahler.SCal

end OAI
