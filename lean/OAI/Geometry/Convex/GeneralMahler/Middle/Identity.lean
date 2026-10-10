import OAI.Geometry.Convex.GeneralMahler.Middle.Poly

namespace OAI
/-! Fval equals actual spectral budget. -/
open Set Filter Real
noncomputable section
namespace GeneralMahler.SCal.Mid
open Grid Profile Segment SE Ft
lemma forB (H:NG)(x y:ℝ)(p:Ft): trav x p.g y=bav p.f (xs x,xs y):=
  trav_bav _ _ (p.test H).cont
lemma vshift {f:ℝ→ℝ}(hf:TestF f)(v:Plane)(c:ℝ):
    bav (fun x=>f x-c) v=bav f v-c:= by
  have he : (fun x=>f x-c)=fun x=>f x + (-c):=by ext;ring
  rw [he,bav_add hf (TestF.const _),bav_const];ring
lemma mvshift {f:ℝ→ℝ}(hf:TestF f)(v:Plane)(c:ℝ):
    bav (fun x=>(f x-c)^2) v = sqav f v -2*c*bav f v+c^2:= by
  have ha : (fun x=>(f x-c)^2)=fun x=> f x ^2 + ((-2*c)*f x+c^2):=by ext;ring
  have hh:= (TestF.const (-2*c)).mul hf
  rw [ha,bav_add (sq_test hf) (hh.add (TestF.const _)),bav_add hh (TestF.const _),bav_const,bav_scale]
  unfold sqav; ring

lemma poly_E (H:NG)(x y:ℝ): Fval x y=symR (xs x,xs y) := by
  let k:=inp x y
  let o:=Op.eval k
  let v:Plane:=(xs x,xs y)
  have hs:=hSeg01 H
  have i0(p:Ft): k 0 p=p.f (xs x):=by simp only [k,inp,ite_eq_left];rfl
  have i1(p:Ft): k 1 p=p.f (xs y):=by norm_num [k,inp];rfl
  have i2(p:Ft): k 2 p=bav p.f v:=by norm_num [k,inp]; apply forB H
  have ha:o Op.ekp=ek v := by
    unfold o; simp only [Op.eval,Op.ekp,i2,i0,i1,Ft.f]
    rw [vshift testK]; unfold ek v; push_cast;  ring
  have hb:o Op.gammaOp=sgamma v:=by
    unfold o
    simp only [Op.eval,Op.gammaOp,Op.q,i1,i0,Ft.f]; unfold sgamma tc Profile.tr v anti mstar
    push_cast; ring
  have hJ(p) : o (Op.dotOp p)=k 2 Q*k p Q+k 2 J*k p J+k 2 V*k p V:=rfl
  have hp : o Op.ru2=Profile.r^2:=by norm_num [o,Op.ru2,Op.q,Op.eval,r]
  have hv (p): o (Op.sm p)=r^2+k p M:=by change o Op.ru2+_= _; rw [hp];rfl
  have h₁ : k 2 Q=bav qu v-q0:=by rw [i2]; apply vshift (hqt H)
  have h₂ : k 2 M = sqav qu v-2*q0*bav qu v+q0^2:=by rw [i2];apply mvshift (hqt H)
  have hj: o (Op.sm 2)-o (Op.dotOp 2)=vsum v:=by
    rw [hv,hJ,h₁,h₂,i2 J,i2 V]
    rw [← PSum v]
    unfold vsum vdis Ft.f; ring
  have hr (p):o (Op.mb p)=o (Op.sm 2)+o (Op.sm p)- 2*o (Op.dotOp p):=by
    change _+ _-Op.eval k (.num 2 1)*_=_
    norm_num [o,Op.eval]
  have hR1:o (Op.mb 1)=pPlus v+qPlus v:=by
    rw [hr,hv,hv,hJ,h₁,h₂,i2 J,i2 V,i1,i1,i1,i1]
    have ht:=PSum v; have h:=lcsq y
    unfold Ft.f; unfold pPlus qPlus mdis; change uc (xs y)^2+us (xs y)^2=_ at h
    unfold v; dsimp only; unfold v at ht; linarith
  have hR0:o (Op.mb 0)=pPlus v.swap+qPlus v.swap:=by
    have hj{f:ℝ→ℝ}(hf:TestF f): sqav f v.swap=sqav f v:=bav_sym (sq_test hf) v
    unfold pPlus qPlus mdis
    rw [hj hs.c_test,hj hs.q_test,hj hs.s_test,bav_sym hs.c_test,bav_sym hs.s_test,bav_sym hs.q_test]
    rw [hr,hv,hv,hJ,h₁,h₂,i2 J,i2 V,i0,i0,i0,i0]
    have ht:=PSum v; have h:=lcsq x
    change uc (xs x)^2+us (xs x)^2=_ at h
    unfold Ft.f v;simpa only [Prod.snd_swap] using (by unfold v at ht;linarith : _)
  have hB(p q):o (Op.bolt p q)=k 2 C-k q C-o (Op.mb p):=rfl
  change o Op.E=symR v
  rw [lid4 _ hs]
  unfold Op.E
  change (o Op.ekp+o Op.gammaOp+
    Op.eval k (.num 10 52)*(o (Op.bolt 0 1)*o (Op.bolt 0 1)+o (Op.bolt 1 0)*o (Op.bolt 1 0))+
    Op.eval k (.num 32 1000)*(o (Op.mb 0)+o (Op.mb 1)))-
    Op.eval k (.num 1064 1000)* (o (Op.sm 2)-o (Op.dotOp 2))=_
  rw [ha,hb,hj,hB,hB,hR0,hR1,i2 C,i1,i0]
  unfold costs pa pd ba bd0 ca0 cd0 tmax lam Ft.f
  rw [vshift testC]; simp only [Op.eval];push_cast; unfold v; dsimp only; ring

lemma efFlip (H:NG)(x y:ℝ):Fval x y=Fval y x:= by
  rw [poly_E H,poly_E H]
  apply Rflip _
end GeneralMahler.SCal.Mid

end

end OAI
