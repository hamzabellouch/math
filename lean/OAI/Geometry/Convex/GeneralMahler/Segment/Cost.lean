import OAI.Geometry.Convex.GeneralMahler.Segment.Mean

namespace OAI
/-! Algebraic reduction of equation (4). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Segment Jet
-- for interval pair v in physical coordinates; subscript a,d average/half-difference
variable (v:Plane)
def pPlus := mdis uc v+mdis us v
def qPlus := mdis qu v
def pa:= (pPlus v+pPlus v.swap)/2
def pd:= (pPlus v-pPlus v.swap)/2
def ba:= (qPlus v+qPlus v.swap)/2
def bd0:= (qPlus v-qPlus v.swap)/2
def ca0:= bav Cp v-(Cp v.2+Cp v.1)/2
def cd0 := (Cp v.2-Cp v.1)/2
def ek:= bav Kp v-(Kp v.2+Kp v.1)/2
def costs:ℝ:= ek v+sgamma v+
  ((ca0 v-pa v-ba v)^2+(cd0 v-pd v-bd0 v)^2)/(4*lam)+ tmax*(pa v+ ba v)

lemma vdis_swap {g:ℝ→ℝ} (hg:TestF g): vdis g v.swap=vdis g v := by
  unfold vdis sqav; rw [bav_sym hg,bav_sym (sq_test hg)]
lemma rsum_eq : rsum v=pPlus v+ qPlus v:=rfl
lemma dsum_eq : dsum v=rsum v-vsum v:=by
  unfold dsum rsum vsum dis mdis vdis; ring
lemma gamma_swap : sgamma v.swap=sgamma v:=by
  unfold sgamma anti; dsimp []; ring
lemma lid4 (H:LayerOK): symR v=costs v-(1+tmax)*vsum v := by
  unfold symR resid costs
  have he : vsum v.swap=vsum v:= by unfold vsum; rw [vdis_swap v H.c_test,vdis_swap v H.s_test,
    vdis_swap v H.q_test]
  rw [gamma_swap, dsum_eq, dsum_eq, he]
  unfold bstar
  rw [rsum_eq,rsum_eq]
  unfold pa pd ba bd0 ca0 cd0 ek rest
  rw [bav_sym testC v,bav_sym testK v]
  unfold lam
  simp only [Prod.fst_swap]; ring

-- Reflection combined with swapping
def refPt (x:Plane):Plane :=(-x.2,-x.1)

lemma bavRefE {f:ℝ→ℝ} (he:Function.Even f)(hf:TestF f):
    bav f (refPt v)=bav f v:=by
  rw [← bav_sym hf (refPt v)]
  have hi (t:ℝ):along (refPt v).swap t= -(along v t):=by unfold refPt along; simp only [Prod.snd_swap,Prod.fst_swap]; ring
  have h (x:ℝ) : f (-x)=f x:=he x
  unfold bav; simp_rw [hi,h]
lemma bavRefO {f:ℝ→ℝ} (he:Function.Odd f)(hf:TestF f):
    bav f (refPt v)= -(bav f v):=by
  rw [← bav_sym hf (refPt v)]
  have hi(t:ℝ):along (refPt v).swap t= -(along v t):=by unfold refPt along; simp only [Prod.snd_swap,Prod.fst_swap]; ring
  have h (x:ℝ):f (-x)= -f x:=he x
  unfold bav; simp_rw [hi,h, intervalIntegral.integral_neg]
lemma mRefE {f:ℝ→ℝ} (he:Function.Even f)(hf:TestF f):
    vdis f (refPt v)=vdis f v ∧ mdis f (refPt v)=mdis f v.swap := by
  have hp := bavRefE v he hf
  have hh : sqav f (refPt v)=sqav f v:=
    bavRefE v (f:=fun x=>f x^2) (fun x=>by change f (-x)^2=f x^2; rw [he]) (sq_test hf)
  constructor
  · unfold vdis;rw [hp,hh]
  unfold mdis; rw [hp,hh]; unfold sqav;rw [bav_sym hf,bav_sym (sq_test hf)]
  unfold refPt;dsimp only;rw [he];rfl
lemma mRefO {f:ℝ→ℝ} (he:Function.Odd f)(hf:TestF f):
    vdis f (refPt v)=vdis f v ∧ mdis f (refPt v)=mdis f v.swap:=by
  have hp:=bavRefO v he hf
  have hh:sqav f (refPt v)=sqav f v:=
    bavRefE v (f:=fun x=>f x^2) (fun x=>by change f (-x)^2=f x^2; rw [he];ring) (sq_test hf)
  constructor
  · unfold vdis; rw [hh,hp];ring
  unfold mdis; rw [hp,hh]; unfold sqav;rw [bav_sym hf,bav_sym (sq_test hf)]
  unfold refPt;simp only [Prod.snd_swap]; rw [he];ring
lemma cost_ref (H:LayerOK): symR (refPt v)=symR v:=by
  rw [lid4 _ H,lid4 _ H]
  have hi:ek (refPt v)=ek v:=by unfold ek; rw [bavRefE v Keven testK]; unfold refPt
                                       ;dsimp only; rw [Keven,Keven]; ring
  have hG:sgamma (refPt v)=sgamma v:=by
    unfold sgamma refPt anti; dsimp only; rw [Keven,Keven,Ceven,Ceven]; ring
  have hA:ca0 (refPt v)=ca0 v:=by
    unfold ca0; rw [bavRefE v Ceven testC]
    unfold refPt;dsimp only;rw [Ceven,Ceven]; ring
  have hD:cd0 (refPt v)= -cd0 v:=by unfold cd0 refPt;dsimp only;rw [Ceven,Ceven];ring
  have hs (v:Plane): (refPt v).swap=refPt v.swap:=rfl
  have hp (v:Plane): pPlus (refPt v)=pPlus v.swap:=by
    unfold pPlus; rw [(mRefE v uc_ref H.c_test).2,(mRefO v us_ref H.s_test).2]
  have hb (v:Plane): qPlus (refPt v)=qPlus v.swap:=(mRefE v H.q_even H.q_test).2
  have hu : vsum (refPt v)=vsum v:=by
    unfold vsum;rw [(mRefE v uc_ref H.c_test).1,(mRefO v us_ref H.s_test).1,(mRefE v H.q_even H.q_test).1]
  unfold costs pa ba pd bd0
  rw [hi,hG,hA,hD,hp,hb,hs,hp,hb,Prod.swap_swap,hu]; ring
lemma neg_left (m h:ℝ): refPt (seg m h)=seg (-m) h:=by
  ext <;> simp [refPt,seg,left,right,xs,sinh_sub,sinh_add] <;> ring
end GeneralMahler.SCal.SE

end

end OAI
