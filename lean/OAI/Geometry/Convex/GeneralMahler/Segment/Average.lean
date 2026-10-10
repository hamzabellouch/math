import OAI.Geometry.Convex.GeneralMahler.Segment.Short

namespace OAI
/-! Uniform endpoint and mean estimates for larger widths. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Jet Segment
variable {m h:ℝ} {f:ℝ→ℝ}

lemma segR (f:ℝ→ℝ)(hf:TestF f)(hh:0≤h)(x y:ℝ)
    (hp:∀ t∈Icc (left m h) (right m h), f (xs t)∈Icc x y):
    bav f (seg m h)∈Icc x y:= by
  rw [bav_norm m h f hf.cont]
  have he:Continuous (fun x=> f (xs (loc m h x))):=(cLC f hf).comp (cLoc ..)
  have h1(t:ℝ)(ht:t∈Icc (-1:ℝ) 1): f (xs (loc m h t))∈Icc x y:=hp _ (loch_local m h t hh ht)
  constructor
  · have hh:=neMono m h continuous_const he (f:=fun _=>x) (fun t ht=>(h1 t ht).1)
    rwa [neConst] at hh
  have hh:=neMono m h he continuous_const (g:=fun _=>y) (fun t ht=>(h1 t ht).2)
  rwa [neConst] at hh

lemma plusR (H:NG)(hh:0≤h)(x y:ℝ)
    (ht:∀ t∈Icc (left m h) (right m h), qu (xs t) ∈ Icc x y) :
    let w:=seg m h; let d:=(y-x)^2
    qPlus w∈Icc 0 d∧ qPlus w.swap∈Icc 0 d := by
  intro v d
  have hl:left m h≤right m h:=by unfold left right; linarith
  have he (t:ℝ):TestF (fun x=>(qu x-t)^2):=sq_test ((hqt H).sub (TestF.const _))
  have hf (w) (hw:w∈Icc x y):
      bav (fun x=>(qu x-w)^2) v∈Icc 0 d:= by
    apply segR _ (he w) hh
    intro t h
    obtain ⟨h1,h2⟩:=ht t h
    unfold d; constructor
    · positivity
    nlinarith [hw.1,hw.2]
  unfold qPlus
  rw [mdis_eq (hqt H),mdis_eq (hqt H),bav_sym (he _) v]
  exact ⟨hf _ (ht _ ⟨hl,le_rfl⟩),hf _ (ht _ ⟨le_rfl,hl⟩)⟩
lemma ik_neg (x:ℝ): ikp (-x)= -ikp x:= by
  have he (x:ℝ): KP0 (-x)=KP0 x:=by unfold KP0; rw [Keven]
  unfold ikp
  have h:=intervalIntegral.integral_comp_neg KP0 (a:=(0:ℝ)) (b:=x)
  simp_rw [he,neg_zero] at h; rw [h, intervalIntegral.integral_symm]

lemma avK (H:NG) {m h:ℝ}(hh:0<h)(he:|left m h| ≤ 14/10)
    (hr:36/10≤right m h):
    bav Kp (seg m h) ≤ 84/10000 := by
  let v:=seg m h
  let x:=v.1;let y:=v.2
  have hx:x<y:=sub_pos.mp (lnv m h hh)
  have hi:= intervalIntegral.integral_mono_on hx.le (testK.cont.intervalIntegrable (μ:=volume) x y)
    (contKP.intervalIntegrable x y) (fun t _=>le_max_right 0 (Kp t))
  have hz: x=xs (left m h):=rfl
  have hu: y=xs (right m h):=rfl
  have hh': (y-x)*bav Kp v ≤ ikp y-ikp x:= by
    have he:=bav_phys Kp testK.cont x y
    have hh:=intervalIntegral.integral_add_adjacent_intervals (contKP.intervalIntegrable (μ:=volume) 0 x)
      (contKP.intervalIntegrable x y)
    unfold ikp
    change (y-x)*bav Kp (x,y) ≤_
    rw [he]; linarith
  have hp: 658/10 ≤ y:= by rw [hu]
                            ;apply x720.trans (x_mono.monotone _);norm_num [nd] at *; exact hr
  have ht₁: x ≤ zn 280:= by
    rw [hz]; unfold zn
    apply x_mono.monotone; have hv:=le_of_abs_le he; norm_num [nd] at *;linarith
  have ht₂:-x≤ zn 280:= by
    rw [hz, ← x_neg]; unfold zn
    apply x_mono.monotone; have hv:=(abs_le.mp he).1; norm_num [nd] at *;linarith
  have ht₃:=area_full H y
  have hv:x ≤686/100:= ht₁.trans x280
  change bav Kp v ≤ _
  apply le_of_mul_le_mul_left (a:=y-x) _ (sub_pos.mpr hx)
  rcases le_total 0 x with hx'|hx'
  · have hi:0 ≤ ikp x:= by
      have he:=ikM hx'
      rw [show ikp 0=0 from by simp [ikp] ] at he;exact he
    linarith
  have he:= (ikM ht₂).trans (area0 H).2; rw [ik_neg] at he
  linarith

-- convex endpoint budget bound
def Yval (x y z:ℝ):=
    -(x+y)/2 + (80/100:ℝ)/mstar^2*((125/100)*(y-x+tc*z)^2+5*Profile.tr^2*z^2)
lemma EK_eq (x:Plane): ek x+sgamma x=bav Kp x+Yval (Kp x.1) (Kp x.2) (Cp x.2-Cp x.1):=by
  unfold ek sgamma anti Yval; ring
lemma Yconv {x y z a b c t:ℝ} (ht:t∈Icc (0:ℝ) 1):
    Yval (mix x a t) (mix y b t) (mix z c t) ≤ mix (Yval x y z) (Yval a b c) t := by
  have hs (x a:ℝ): mix x a t ^2 ≤ mix (x^2) (a^2) t := by
    have h:= mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg (x-a))
    unfold mix; linarith
  have h1:=hs z c;have h2:= hs (y-x+tc*z) (b-a+tc*c)
  unfold Yval mix tc Profile.tr mstar at *
  norm_num at *;linarith
lemma Ybound (A B C D E F:ℝ) (x y z K:ℝ)(ha:A≤x)(hb:x≤B)(hc:C≤y)(hd:y≤D)(he:E≤z)(hf:z≤F)
    (h:∀ x:ℝ,x∈ ({A,B}:Set ℝ)→∀ y:ℝ,y∈ ({C,D}:Set ℝ)→
      ∀ z:ℝ,z∈ ({E,F}:Set ℝ)→ Yval x y z ≤ K):
    Yval x y z ≤ K:=by
  obtain ⟨a,ha,hxa⟩:=mix_exists ha hb
  obtain ⟨b,hb,hxb⟩:=mix_exists hc hd
  obtain ⟨c,hc,hxc⟩:=mix_exists he hf
  have hs {x y:ℝ}(a:ℝ)(ha:a∈Icc (0:ℝ) 1) (he:x≤K)(hf:y≤K):mix x y a≤ K:=by
    unfold mix
    have hi:= mul_le_mul_of_nonneg_left he (sub_nonneg.mpr ha.2)
    have hh:= mul_le_mul_of_nonneg_left hf ha.1;linarith
  have heq (x y:ℝ):mix x x y=x:=by unfold mix; ring
  have H (x:ℝ)(hx:x∈ ({A,B}:Set ℝ)) (y:ℝ)(hy:y∈ ({C,D}:Set ℝ)):
      Yval x y z≤ K:= by
    rw [hxc]
    have hi:= (Yconv hc).trans (hs c hc (h x hx y hy E (by simp)) (h x hx y hy F (by simp)))
    rwa [heq,heq] at hi
  have hh(x:ℝ)(hx:x∈ ({A,B}:Set ℝ)): Yval x y z≤K:= by
    rw [hxb]
    have hi:= (Yconv hb).trans (hs b hb (H x hx C (by simp)) (H x hx D (by simp)))
    rwa [heq,heq] at hi
  rw [hxa];have hi:= (Yconv ha).trans (hs a ha (hh A (by simp)) (hh B (by simp)))
  rwa [heq,heq] at hi
end GeneralMahler.SCal.SE

end

end OAI
