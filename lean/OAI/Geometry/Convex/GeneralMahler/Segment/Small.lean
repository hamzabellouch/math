import OAI.Geometry.Convex.GeneralMahler.Segment.Phase
import OAI.Geometry.Convex.GeneralMahler.Segment.Omega

namespace OAI
/-! Small angle scale estimates. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Jet
local notation "w" => Profile.omegaP
def wp:= r^2*w^2
def ubase (h:ℝ):= wp*h^2/3
def qsmall (h:ℝ):= (1-2*w^4*h^2/(15*(1+w^2)))/(1+h^2/3)
lemma wp_pos:0<wp:=by unfold wp Profile.r Profile.omegaP; norm_num
lemma omega_pos:0<w:=by norm_num [Profile.omegaP]
variable {h:ℝ}
lemma ubP (hh:0<h): 0<ubase h:=by unfold ubase; have hi:=wp_pos; positivity

lemma sfL (hh:0<h): ubase h*qsmall h ≤ fstar h := by
  have hp:0<sinh h:=Real.sinh_pos_iff.mpr hh
  have hs:= sh3 h hh.le
  have hi: h^2+h^4/3 ≤ sinh h^2 := by
    apply le_trans _ (show (h+h^3/6)^2 ≤ sinh h^2 from pow_le_pow_left₀ (by positivity) hs _)
    nlinarith [show 0≤h^6 by positivity]
  have he:=snsq (w*h) (by have ht:=omega_pos; positivity)
  let s:= (w*h)^2-(w*h)^4/3+2*(w*h)^6/45
  have hb : sin (w*h)^2/sinh h^2 ≤ s/(h^2+h^4/3) := by
    apply div_le_div₀ (show 0 ≤ s from (sq_nonneg _).trans he) he (by positivity) hi
  unfold fstar
  have H : 0 < 1+w^2:=by positivity
  apply le_trans _ (show _ ≤ (r^2/(1+w^2))*(w^2- sin (w*h)^2/sinh h^2)
    from mul_le_mul_of_nonneg_left (sub_le_sub_left hb (w^2)) (by positivity))
  apply le_of_eq
  unfold qsmall ubase s wp
  field_simp;ring

lemma smallD (m:ℝ)(hh:0<h): |Pdstar m h| ≤ 2*h*ubase h := by
  let s:=w*h
  have hp:0 ≤ s:=mul_nonneg omega_pos.le hh.le
  have hi:|sin s| ≤ s:=by simpa [abs_of_nonneg hp] using (Real.abs_sin_le_abs (x:=s))
  have He := coth_est hh
  have he:=sinDif s hp
  have hz: |tanh m| ≤1 := by
    rw [← th_eq]; have hi:=ri0 m
    nlinarith [hi.2,sq_abs (thR m)]
  have hb : |PhiB h| ≤ w*h^2/3 := by
    unfold PhiB
    let v:=cott h-1/h
    have hv:0≤v ∧ v≤ h/3:= He
    have hj : cott h*sin s-w*cos s=v*sin s+(sin s-s*cos s)/h := by unfold s v; field_simp;ring
    change |(cott h*sin s-w*cos s)/_|≤_
    rw [hj,abs_div,abs_of_nonneg (show 0≤1+w^2 by positivity),
      div_le_iff₀ (show 0<1+w^2 by positivity)]
    apply (abs_add_le ..).trans
    rw [abs_mul, abs_div,abs_of_nonneg hv.1, abs_of_pos hh]
    apply le_trans (add_le_add (mul_le_mul hv.2 hi (abs_nonneg _) (by positivity))
      (div_le_div_of_nonneg_right he hh.le))
    unfold s; apply le_of_eq; field_simp
  unfold Pdstar; simp only [abs_mul]
  have hr : (0:ℝ)≤ Profile.r:=by norm_num [Profile.r]
  have hm : |-2| * |Profile.r^2|=(2:ℝ)*Profile.r^2:=by norm_num [abs_of_nonneg (sq_nonneg Profile.r)]
  rw [hm]
  have hq := mul_le_mul hb hz (abs_nonneg _) (by have ht:=omega_pos; positivity)
  have ht:= mul_le_mul hq hi (abs_nonneg _) (by have ht:=omega_pos; positivity)
  unfold ubase wp s at *
  nlinarith [mul_le_mul_of_nonneg_left ht (show 0≤2*r^2 by positivity)]

-- exact relaxed constants for W and cosh/s
lemma shr16 (hh:0<h)(he:h≤16/100):
    shv h ≤ 10044/10000 ∧ cosh h ≤ 1014/1000:= by
  have hs:= smallConst.1
  have h1:=sinhH hs hh.le he
  have hg: |h|≤16/100:=by rwa [abs_of_pos hh]
  constructor
  · unfold shv
    rw [div_le_iff₀ hh]
    nlinarith [mul_nonneg hh.le (show 0≤ (16/100:ℝ)^2-h^2 by nlinarith)]
  exact le_trans (cosh_le_cosh.mpr (by rw [abs_of_pos hh,abs_of_pos (show (0:ℝ)<16/100 by norm_num)]; exact he)) hs

lemma mean_beta2:mean0 (fun x:ℝ=>x^2)=1/3:=by
  unfold mean0; rw [integral_pow]; norm_num
lemma mean_beta4:mean0 (fun x:ℝ=>x^4)=1/5:=by
  unfold mean0; rw [integral_pow]; norm_num

lemma Wshr (m:ℝ)(hh:0<h)(he:h≤16/100):
    (∀ x∈Icc (-1:ℝ) 1,0≤omega m h x ∧ omega m h x ≤ 1507/1000) ∧
      mean0 (omega m h) ≤ 1012/1000:= by
  have hs:= sh0 hh
  obtain ⟨ha,hb⟩:=shr16 hh he
  constructor
  · intro x hx; exact ⟨om0 m h hh x hx,by linarith [Wmax m hh x]⟩
  let r:=(3/4:ℝ)*shv h*(1+cosh h)
  have hi : mean0 (omega m h) ≤ mean0 (fun x:ℝ=>r*(1-x^2)) :=
    mean_mono (omCont ..) (by fun_prop) (Wpar m hh)
  apply hi.trans
  rw [mean_scale,mean_sub (continuous_const) (show Continuous (fun x:ℝ=>x^2) by fun_prop),mean_const,
    mean_beta2]
  unfold r; nlinarith

lemma mβ (m:ℝ)(hh:0<h)(he:h≤3/10):
    normE m h (fun x:ℝ=> x^2) ≤1/3+(5/100)*h^2:=by
  let f:=fun x:ℝ=> de m h x * x^2
  let c:= cosh m
  have hp:=normp m h
  have hz:0<c:=cosh_pos _
  have hf:Continuous f:=(cDe ..).mul (by fun_prop)
  have h₁ : mean0 f=c*mean0 (fun x=>cosh (h*x)*x^2) := by
    have hi (x:ℝ): f x + f (-x)= (2*c)*(cosh (h*x)*x^2) := by
      unfold f de loc c; simp only [mul_neg,Real.cosh_add, Real.cosh_neg, Real.sinh_neg]; ring
    have ht:=mean_add (f:=f) hf (hf.comp continuous_neg)
    change mean0 (fun x=>f x+f (-x))= mean0 f+mean0 (fun x=>f (-x)) at ht
    simp_rw [hi] at ht; rw [mean_ref,mean_scale] at ht; linarith
  have hq:mean0 (fun x:ℝ=> cosh (h*x)*x^2) ≤
      (1/3:ℝ)+(1046/1000)*h^2/10:= by
    have hi:=mean_mono (f:=fun x:ℝ=>cosh (h*x)*x^2)
      (g:=fun x:ℝ=> x^2+((1046/1000:ℝ)*h^2/2)*x^4) (by fun_prop) (by fun_prop) ?_
    · rw [mean_add (by fun_prop) (show Continuous (fun x:ℝ=>((1046/1000)*h^2/2)*x^4) by fun_prop),
        mean_beta2,mean_scale,mean_beta4] at hi
      linarith
    intro x hx
    have h : |h*x| ≤3/10 := by rw [abs_mul,abs_of_pos hh]; apply le_trans (mul_le_of_le_one_right hh.le (abs_le.mpr hx)) he
    have hv:= cshH smallConst.2 h
    nlinarith [mul_le_mul_of_nonneg_right hv (sq_nonneg x)]
  unfold normE; change mean0 f / normM m h ≤ _
  rw [div_le_iff₀ hp,h₁]
  apply le_trans (mul_le_mul_of_nonneg_left hq hz.le)
  have hI := sh3 h hh.le
  have hv : c*(1+h^2/6)≤normM m h:=by
    apply le_of_mul_le_mul_left (a:=h) _ hh
    rw [nor_eq]
    nlinarith
  apply le_trans _ (mul_le_mul_of_nonneg_left hv (by positivity))
  have hi : (1/3:ℝ)+ (1046/1000)*h^2/10≤ (1/3+5/100*h^2)*(1+h^2/6):=by
    nlinarith [sq_nonneg h,sq_nonneg (h^2)]
  nlinarith [mul_le_mul_of_nonneg_left hi hz.le]
end GeneralMahler.SCal.SE

end

end OAI
