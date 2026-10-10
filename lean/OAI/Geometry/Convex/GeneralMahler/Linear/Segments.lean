import OAI.Geometry.Convex.GeneralMahler.Linear.Powers

namespace OAI
/-! End point profile tests for Eq26-27. Segment condition Eq4 (proved in scalar part). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace Interval
namespace GeneralMahler
namespace Segment
open Profile

lemma Wav {f:ℝ→ℝ} (hf:TestF f) : Bwt (bav f) := ⟨bav_con hf.cont,bav_bound hf.poly⟩
lemma bav_sym {f:ℝ→ℝ} (hf:TestF f) (u:Plane): bav f u.swap=bav f u := by
  obtain ⟨x,y⟩:=u
  rcases eq_or_ne x y with h|h
  · subst x; rfl
  have ht := pl_test hf
  have h1 := delta_eq ht x y
  have h2 := delta_eq ht y x
  rw [pl_d hf] at h1 h2
  change bav f (y,x)= bav f (x,y)
  apply mul_right_cancel₀ (show x-y≠0 from sub_ne_zero.mpr h)
  linear_combination h1 + h2

lemma bav_add {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) (u:Plane) :
    bav (fun x=>f x+g x) u=bav f u+bav g u := by
  have ha : Continuous (along u) := by unfold along; fun_prop
  exact intervalIntegral.integral_add ((hf.cont.comp ha).intervalIntegrable ..)
    ((hg.cont.comp ha).intervalIntegrable ..)
lemma bav_scale (f:ℝ→ℝ) (u:Plane) (c:ℝ):
    bav (fun x=>c*f x) u=c*bav f u := by unfold bav; rw [intervalIntegral.integral_const_mul]
lemma bav_const (c:ℝ) (u:Plane): bav (fun _=>c) u=c := by simp [bav]
lemma Wflip {f:Plane→ℝ} (hf:Bwt f) : Bwt (fun x:Plane=> f x.swap) :=
  ⟨hf.c.comp continuous_swap,hf.p.comp (PolyBound.snd.prodMk PolyBound.fst)⟩
lemma Wsq {f:Plane→ℝ} (hf:Bwt f): Bwt (fun x=> f x^2) := by simp_rw [pow_two]; exact hf.mul hf

/-- remainder of scalar profile. bstar uses A profile. -/
def rest (f:ℝ→ℝ) (u:Plane) := bav f u-f u.1
def dis (f:ℝ→ℝ) (u:Plane) := bav f u-f u.2
def sqav (f:ℝ→ℝ) (u:Plane) := bav (fun z=> f z^2) u
def mdis (f:ℝ→ℝ) (u:Plane) := sqav f u-2*bav f u*f u.2 + f u.2^2
def vdis (f:ℝ→ℝ) (u:Plane) := sqav f u-(bav f u)^2
def vsum (u:Plane) := vdis uc u+vdis us u+vdis qu u
def rsum (u:Plane) := mdis uc u+mdis us u+mdis qu u
def dsum (u:Plane) := dis uc u^2+dis us u^2+dis qu u^2
def bstar (u:Plane) := rest Cp u-rsum u
def anti (u:Plane) (f:ℝ→ℝ) := f u.2-f u.1
def sgamma (u:Plane) :=
  ((80/100)/mstar^2)*(125/100*(anti u Kp+tc*anti u Cp)^2+5*Profile.tr^2*anti u Cp^2)
def resid (u:Plane) :=
  rest Kp u+sgamma u+(1/(4*lam))*bstar u^2 + tmax*dsum u-vsum u
def symR (u:Plane) := (1/2:ℝ)*(resid u+resid u.swap)
def SegmentOK := ∀ x y:ℝ,x<y→ symR (x,y)<0

variable {f:ℝ→ℝ}
lemma mdis_eq (hf:TestF f) (u:Plane): mdis f u=bav (fun z=>(f z-f u.2)^2) u := by
  let c := (-2)*f u.2
  have he : (fun z=> (f z-f u.2)^2)=fun z=> f z^2+c*f z+ f u.2^2 := by
    ext; unfold c; ring
  have hh := sq_test hf
  have hi := (TestF.const c).mul hf
  unfold mdis sqav
  rw [he,bav_add (hh.add hi) (TestF.const _),bav_add hh hi,bav_scale,bav_const]
  unfold c; ring
lemma Wr (hf:TestF f): Bwt (rest f) := (Wav hf).sub (Bwt.fst hf)
lemma Ws (hf:TestF f): Bwt (dis f) := (Wav hf).sub (Bwt.snd hf)
lemma Wm (hf:TestF f): Bwt (mdis f) :=
  ((Wav (sq_test hf)).sub (((Bwt.const _).mul (Wav hf)).mul (Bwt.snd hf))).add
    (Bwt.snd (sq_test hf))
lemma Wv (hf:TestF f): Bwt (vdis f) :=
  (Wav (sq_test hf)).sub (Wsq (Wav hf))
lemma Wa (hf:TestF f): Bwt (fun u=> anti u f) := (Bwt.snd hf).sub (Bwt.fst hf)
lemma Wg : Bwt sgamma :=
  (Bwt.const _).mul
    (((Bwt.const _).mul (Wsq ((Wa testK).add ((Bwt.const _).mul (Wa testC))))).add
      ((Bwt.const _).mul (Wsq (Wa testC))))
lemma Wd (h:LayerOK) : Bwt dsum :=
  ((Wsq (Ws h.c_test)).add (Wsq (Ws h.s_test))).add (Wsq (Ws h.q_test))
lemma Wb (h:LayerOK) : Bwt bstar :=
  (Wr testC).sub (((Wm h.c_test).add (Wm h.s_test)).add (Wm h.q_test))
lemma Wvs (h:LayerOK) : Bwt vsum :=
  ((Wv h.c_test).add (Wv h.s_test)).add (Wv h.q_test)
lemma Wres (h:LayerOK) : Bwt resid :=
  ((((Wr testK).add Wg).add ((Bwt.const _).mul (Wsq (Wb h)))).add
    ((Bwt.const _).mul (Wd h))).sub (Wvs h)
lemma WR (h:LayerOK) : Bwt symR :=
  (Bwt.const _).mul ((Wres h).add (Wflip (Wres h)))

lemma diagR (x:ℝ) : symR (x,x)=0 := by
  have he : resid (x,x)=0 := by
    simp_rw [resid,rest,bstar,vsum,rsum,dsum,sgamma,anti,rest,dis,vdis,mdis,sqav,bav_same]
    ring
  unfold symR
  change (1/2:ℝ)*(resid (x,x)+resid (x,x))=_
  rw [he]; ring
lemma Rflip (x:Plane) : symR x=symR x.swap := by simp [symR,add_comm]
lemma negR (h:SegmentOK) (u:Plane) (hu:u.1≠u.2): symR u<0 := by
  obtain ⟨x,y⟩:=u
  rcases lt_or_gt_of_ne hu with hi|hi
  · exact h _ _ hi
  rw [Rflip]; exact h _ _ hi
lemma Rle (h:SegmentOK) (u:Plane) : symR u≤0 := by
  obtain ⟨x,y⟩:=u
  rcases eq_or_ne x y with he|he
  · subst x; rw [diagR]
  exact le_of_lt (negR h _ he)
end Segment
end GeneralMahler

end

end OAI
