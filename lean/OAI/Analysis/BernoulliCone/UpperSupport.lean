import OAI.Analysis.BernoulliCone.CylindricalCalculus

namespace OAI

section
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison.UpperAlgebra
def flo (u:ℝ) :ℝ := (8+u*(-40+u*(40+u*(-8+u*((-8/7:ℝ)+u*((-8/21:ℝ)+u*((-40/231:ℝ)+u*((-460/33:ℝ)+u*(150/11:ℝ)))))))))

def fhi (u:ℝ) :ℝ := (8+u*(-40+u*(40+u*(-8+u*((-8/7:ℝ)+u*((-8/21:ℝ)+u*((-40/231:ℝ)+u*((35/33:ℝ)+u*(-15/11:ℝ)))))))))

def numerator (u F:ℝ) :ℝ := 9*u*(1-u)*(1+u)^2*F^2+
  ((1-6*u-3*u^2)*F-8*(1+u))^2
def denominator (u:ℝ) :ℝ := 64*u*(1-u)^5*(1+u)^2
def bern_lo (x:ℝ) :ℝ :=
 (8963403802771821580584196553916675261935501120693147951646273/14551915228366851806640625000000000000000000000000000000000000:ℝ)*x^0*(1-x)^19 +
 (489924829765456954778865308004779162353303628212611757632243/36379788070917129516601562500000000000000000000000000000000:ℝ)*x^1*(1-x)^18 +
 (49769555037754151943109135153056907940324983405814454742197/363797880709171295166015625000000000000000000000000000000:ℝ)*x^2*(1-x)^17 +
 (241171544309613921452176651513547035701117488149602398545521/280124368146061897277832031250000000000000000000000000000:ℝ)*x^3*(1-x)^16 +
 (813419086138655742693400878597426747137820729361029314453283/215695763472467660903930664062500000000000000000000000000:ℝ)*x^4*(1-x)^15 +
 (26390534901568505873385225990643235317241761460076963637719/2156957634724676609039306640625000000000000000000000000:ℝ)*x^5*(1-x)^14 +
 (164606421874770730021787386234243493522999746324215690279/5392394086811691522598266601562500000000000000000000:ℝ)*x^6*(1-x)^13 +
 (12937649845297388757164077325683850040267461146379488389/215695763472467660903930664062500000000000000000000:ℝ)*x^7*(1-x)^12 +
 (406574381504531640456151479204496276555618768129464927/4313915269449353218078613281250000000000000000000:ℝ)*x^8*(1-x)^11 +
 (234332377637560595227876241971859462384073890057109/1960870577022433280944824218750000000000000000:ℝ)*x^9*(1-x)^10 +
 (1203984888564608030855581683826211128963939859577/9804352885112166404724121093750000000000000:ℝ)*x^10*(1-x)^9 +
 (2506388470738655109137023670431246929874450257/24510882212780416011810302734375000000000:ℝ)*x^11*(1-x)^8 +
 (16837782271327404835800216484886618277280203/245108822127804160118103027343750000000:ℝ)*x^12*(1-x)^7 +
 (723289103741917289394757467584219903883291/19608705770224332809448242187500000000:ℝ)*x^13*(1-x)^6 +
 (47755665140733764406977363749637036181/3063860276597552001476287841796875:ℝ)*x^14*(1-x)^5 +
 (109117483702727600919378994299975467223/21569576347246766090393066406250000:ℝ)*x^15*(1-x)^4 +
 (1047331065768340618289444397103804113/862783053889870643615722656250000:ℝ)*x^16*(1-x)^3 +
 (436047208669296315095634434961738/2156957634724676609039306640625:ℝ)*x^17*(1-x)^2 +
 (255902850597815514061767304524/12325472198426723480224609375:ℝ)*x^18*(1-x)^1 +
 (3394151041074323326944784128/3451132215559482574462890625:ℝ)*x^19*(1-x)^0

lemma identity_lo (x:ℝ) :
    17734/1000*denominator (729/2500+171/2500*x)-
      numerator (729/2500+171/2500*x) (flo (729/2500+171/2500*x))=bern_lo x := by
  unfold denominator numerator flo bern_lo
  ring
lemma bound_lo {u:ℝ} (hl:729/2500≤u) (hr:u≤9/25) :
    numerator u (flo u) ≤ 17734/1000*denominator u := by
  let x:ℝ := (u-729/2500)/(171/2500)
  have hx:0≤x := by dsimp [x]; linarith
  have hx1:x≤1 := by dsimp [x]; linarith
  have he:u=729/2500+171/2500*x := by dsimp [x]; ring
  have hh:0≤bern_lo x := by
    have hy:0≤1-x:=sub_nonneg.mpr hx1
    unfold bern_lo
    positivity
  have hid:=identity_lo x
  rw [←he] at hid
  linarith
def bern_hi (x:ℝ) :ℝ :=
 (849523188772202062952127582590706450849117609037139000351019273/1455191522836685180664062500000000000000000000000000000000000000:ℝ)*x^0*(1-x)^19 +
 (93179306357846201343445973374906275904817545892951388839542101/7275957614183425903320312500000000000000000000000000000000000:ℝ)*x^1*(1-x)^18 +
 (18974602329449808545744283216823565346085275621762543853178403/145519152283668518066406250000000000000000000000000000000000:ℝ)*x^2*(1-x)^17 +
 (822165382959604220103480910444756120428984820375372799568597/1000444171950221061706542968750000000000000000000000000000:ℝ)*x^3*(1-x)^16 +
 (310839707059004093165581312310472350330992935722408242942327377/86278305388987064361572265625000000000000000000000000000000:ℝ)*x^4*(1-x)^15 +
 (5044142694946429551001220955882851233800847971499479484212663/431391526944935321807861328125000000000000000000000000000:ℝ)*x^5*(1-x)^14 +
 (251668014204735969749054760546283303474370942339591664607899/8627830538898706436157226562500000000000000000000000000:ℝ)*x^6*(1-x)^13 +
 (1235634399554121908924030947860850986652889899126252252659/21569576347246766090393066406250000000000000000000000:ℝ)*x^7*(1-x)^12 +
 (77589953736219644144344335770737845793137550523323731459/862783053889870643615722656250000000000000000000000:ℝ)*x^8*(1-x)^11 +
 (44660548374712752221624841808257378586562188161986073/392174115404486656188964843750000000000000000000:ℝ)*x^9*(1-x)^10 +
 (916250005076041111106254606666895886986689057674891/7843482308089733123779296875000000000000000000:ℝ)*x^10*(1-x)^9 +
 (951585875820484883100134663640175605694076953623/9804352885112166404724121093750000000000000:ℝ)*x^11*(1-x)^8 +
 (51000683351293175464330418461775052425785022601/784348230808973312377929687500000000000000:ℝ)*x^12*(1-x)^7 +
 (136459634108357108721466303242775319311756947/3921741154044866561889648437500000000000:ℝ)*x^13*(1-x)^6 +
 (1148423078874808213210387852442026970758371/78434823080897331237792968750000000000:ℝ)*x^14*(1-x)^5 +
 (10196766646349518045449719053047121364523/2156957634724676609039306640625000000:ℝ)*x^15*(1-x)^4 +
 (12153537895134647265778113696039851901/10784788173623383045196533203125000:ℝ)*x^16*(1-x)^3 +
 (10034649455828992505480875647694257/53923940868116915225982666015625:ℝ)*x^17*(1-x)^2 +
 (5823221991208531503907222896876/308136804960668087005615234375:ℝ)*x^18*(1-x)^1 +
 (76044167690309330248836548352/86278305388987064361572265625:ℝ)*x^19*(1-x)^0

lemma identity_hi (x:ℝ) :
    17734/1000*denominator (729/2500+171/2500*x)-
      numerator (729/2500+171/2500*x) (fhi (729/2500+171/2500*x))=bern_hi x := by
  unfold denominator numerator fhi bern_hi
  ring
lemma bound_hi {u:ℝ} (hl:729/2500≤u) (hr:u≤9/25) :
    numerator u (fhi u) ≤ 17734/1000*denominator u := by
  let x:ℝ := (u-729/2500)/(171/2500)
  have hx:0≤x := by dsimp [x]; linarith
  have hx1:x≤1 := by dsimp [x]; linarith
  have he:u=729/2500+171/2500*x := by dsimp [x]; ring
  have hh:0≤bern_hi x := by
    have hy:0≤1-x:=sub_nonneg.mpr hx1
    unfold bern_hi
    positivity
  have hid:=identity_hi x
  rw [←he] at hid
  linarith
end Bernoulli.DeSilvaJerison.UpperAlgebra

namespace Bernoulli.DeSilvaJerison

/-- For τ=-2 the auxiliary Legendre solution is elementary and rational. -/
def gSup (t:ℝ) :ℝ := (1+t^2)/(1-t^2)^2
def gSup1 (t:ℝ) :ℝ := 2*t*(3+t^2)/(1-t^2)^3
def qSup (t:ℝ) :ℝ := 2*t*(3+t^2)/((1-t^2)*(1+t^2))
def qSup1 (t:ℝ) :ℝ := (6*t*qSup t+6)/(1-t^2)-(qSup t)^2
def GSup (t:ℝ) :ℝ := 9*(f t)^2+(1-t^2)*(fp t-f t*qSup t)^2

lemma gSup_pos {t:ℝ} (ht:|t|<1) :0<gSup t := by
  have hd:0<1-t^2 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  unfold gSup
  positivity

lemma hasDerivAt_gSup {t:ℝ} (ht:|t|<1) : HasDerivAt gSup (gSup1 t) t := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  convert! (((hasDerivAt_const t (1:ℝ)).add ((hasDerivAt_id t).pow 2)).div
    (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).pow 2)
    (pow_ne_zero 2 hd)) using 1
  norm_num only [gSup1,id_eq,pow_one,Pi.add_apply,Pi.sub_apply,Pi.pow_apply]
  field_simp [hd]
  ring

lemma qSup_eq {t:ℝ} (ht:|t|<1) : qSup t=gSup1 t/gSup t := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  have hp:1+t^2≠0 := by positivity
  unfold qSup gSup gSup1
  field_simp

lemma hasDerivAt_qSup {t:ℝ} (ht:|t|<1) : HasDerivAt qSup (qSup1 t) t := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  have hp:1+t^2≠0 := by positivity
  have hT:=(hasDerivAt_id t).pow 2
  convert! ((((hasDerivAt_id t).const_mul 2).mul ((hasDerivAt_const t (3:ℝ)).add hT)).div
    (((hasDerivAt_const t (1:ℝ)).sub hT).mul ((hasDerivAt_const t (1:ℝ)).add hT))
    (mul_ne_zero hd hp)) using 1
  norm_num only [qSup1,qSup,id_eq,pow_one,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
  field_simp [hd,hp]
  ring

lemma hasDerivAt_GSup {t:ℝ} (ht:t∈Ioo (-1:ℝ) 1) :
    HasDerivAt GSup (2*((5*t-(1-t^2)*qSup t)*(fp t-f t*qSup t)^2-
      3*f t*(fp t-4*f t*qSup t))) t := by
  have hh:=(((hasDerivAt_f ht).pow 2).const_mul 9).add
    (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).mul
      (((hasDerivAt_fp ht).sub ((hasDerivAt_f ht).mul (hasDerivAt_qSup (abs_lt.mpr ht)))).pow 2))
  have hd:1-t^2≠0 := by nlinarith [ht.1,ht.2]
  have hR:=f_relation ht
  have hODE:(1-t^2)*(-6/(1-t^2)^4)=6*t*fp t-6*f t := by
    field_simp at hR ⊢
    nlinarith
  convert! hh using 1
  norm_num only [id_eq,pow_one,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
  have hF : -6/(1-t^2)^4=(6*t*fp t-6*f t)/(1-t^2) := by
    apply (eq_div_iff hd).mpr
    nlinarith [hODE]
  rw [hF]
  unfold qSup1
  field_simp [hd]
  ring

lemma upper_endpoint_bounds : -1/8≤f (27/50) ∧ fp (1/2)≤-4 := by
  constructor
  · have hh:=f_series_lower 6 (t:=27/50) (by norm_num) (by norm_num)
    norm_num [B,Finset.sum_range_succ] at hh ⊢
    linarith
  · have hh:=fp_series_upper 1 (t:=1/2) (by norm_num) (by norm_num)
    norm_num [B,Finset.sum_range_succ] at hh ⊢
    linarith

lemma qSup_small {t:ℝ} (h0:0≤t) (hb:t≤27/50) :
    0≤qSup t ∧ qSup t≤4 ∧ 5*t≤(1-t^2)*qSup t := by
  have hd:0<1-t^2:=by nlinarith
  have hp:0<1+t^2:=by positivity
  have hu:t^2≤729/2500 := by nlinarith
  constructor
  · unfold qSup; positivity
  constructor
  · rw [qSup,div_le_iff₀ (mul_pos hd hp)]
    have h1:2*t*(3+t^2)≤(27/25:ℝ)*(3+729/2500) := by
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    have h2:(1-t^2)*(1+t^2)≥1-(729/2500:ℝ)^2 := by nlinarith [sq_nonneg (t^2-729/2500)]
    nlinarith
  · have he:(1-t^2)*qSup t-5*t=t*(1-3*t^2)/(1+t^2) := by
      unfold qSup
      field_simp [ne_of_gt hd,ne_of_gt hp]
      ring
    have hz:0≤1-3*t^2 := by nlinarith
    have hh:0≤t*(1-3*t^2)/(1+t^2) := by positivity
    linarith

lemma GSup_nonpos_deriv {t:ℝ} (hl:t7≤t) (hr:t≤27/50) : deriv GSup t≤0 := by
  have ht0:0≤t:=t7_pos.le.trans hl
  have ht1:t<1:=by linarith
  have hI:t∈Ioo (-1:ℝ) 1:=⟨by linarith,ht1⟩
  have hf0:f t≤0 := by
    have hh:=f_strictAnti.antitoneOn ⟨t7_pos.le,t7_lt_one⟩ ⟨ht0,ht1⟩ hl
    simpa only [f_t7] using hh
  have hf:-1/8≤f t := upper_endpoint_bounds.1.trans
    (f_strictAnti.antitoneOn ⟨ht0,ht1⟩ (by norm_num) hr)
  have hp:fp t≤-4 := (fp_strictAnti.antitoneOn (by norm_num) ⟨ht0,ht1⟩
    (by linarith [t7_bounds.1])).trans upper_endpoint_bounds.2
  obtain ⟨hq0,hq4,hqL⟩:=qSup_small ht0 hr
  have hm:=mul_le_mul_of_nonneg_left hq4 (show 0≤-f t by linarith)
  have hB:fp t-4*f t*qSup t≤0 := by nlinarith
  rw [(hasDerivAt_GSup hI).deriv]
  have hh1:=mul_nonpos_of_nonpos_of_nonneg (show 5*t-(1-t^2)*qSup t≤0 by linarith)
    (sq_nonneg (fp t-f t*qSup t))
  have hh2:=mul_nonneg_of_nonpos_of_nonpos hf0 hB
  nlinarith

lemma GSup_near {t:ℝ} (hl:t7≤t) (hr:t≤27/50) : GSup t≤c7 := by
  have hanti:AntitoneOn GSup (Icc t7 (27/50)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro x hx
      exact (hasDerivAt_GSup ⟨by linarith [hx.1,t7_pos],by linarith [hx.2]⟩).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_GSup ⟨by linarith [hx.1,t7_pos],by linarith [hx.2]⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact GSup_nonpos_deriv hx.1.le hx.2.le
  have he:GSup t7=c7 := by simp [GSup,f_t7,c7]
  rw [←he]
  exact hanti ⟨le_rfl,by linarith [t7_bounds.2]⟩ ⟨hl,hr⟩ hl

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison

lemma c7_lower : 17734/1000≤c7 := by
  have hl:t7^2≤(517331/1000000:ℝ)^2 := by nlinarith [t7_bounds.2,t7_pos]
  have hu:1-t7^2≤1-(517330/1000000:ℝ)^2 := by nlinarith [t7_bounds.1,t7_pos]
  have hd:0<1-t7^2 := by nlinarith [t7_pos,t7_lt_one]
  have hp:=pow_le_pow_left₀ hd.le hu 5
  have hm:=mul_le_mul hl hp (by positivity : (0:ℝ)≤(1-t7^2)^5) (by norm_num)
  rw [c7_eq]
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos t7_pos) (pow_pos hd 5))).mpr
  nlinarith

lemma numerator_scaled_bounds {t:ℝ} (hl:0≤t) (hr:t<1) :
    UpperAlgebra.flo (t^2) ≤ 8*(1-t^2)^2*f t ∧
      8*(1-t^2)^2*f t≤UpperAlgebra.fhi (t^2) := by
  have hd:0<1-t^2:=by nlinarith
  have hL:=f_series_lower 6 hl hr
  have hU: f t≤(8-25*t^2+15*(t^2)^2)/(8*(1-t^2)^2)-15/8*t^2*B 6 (t^2) := by
    have hh := mul_le_mul_of_nonneg_left (A_series_bounds 6 hl hr).1 (show (0:ℝ)≤15/8*t by positivity)
    unfold f
    have hp : (t^2)^2=t^4 := by ring
    rw [hp]
    linear_combination hh
  constructor
  · have he:UpperAlgebra.flo (t^2)/(8*(1-t^2)^2)=
        (8-25*t^2+15*(t^2)^2)/(8*(1-t^2)^2)-15/8*t^2*(B 6 (t^2)+(t^2)^6/(1-t^2)) := by
      unfold UpperAlgebra.flo B
      norm_num [Finset.sum_range_succ]
      field_simp [ne_of_gt hd]
      ring
    rw [←he] at hL
    exact (div_le_iff₀ (by positivity)).mp hL |>.trans_eq (mul_comm _ _)
  · have he:UpperAlgebra.fhi (t^2)/(8*(1-t^2)^2)=
        (8-25*t^2+15*(t^2)^2)/(8*(1-t^2)^2)-15/8*t^2*B 6 (t^2) := by
      unfold UpperAlgebra.fhi B
      norm_num [Finset.sum_range_succ]
      field_simp [ne_of_gt hd]
      ring
    rw [←he] at hU
    simpa only [mul_comm] using (le_div_iff₀ (by positivity)).mp hU

lemma quadratic_bound {A B C L H X R:ℝ} (hA:0≤A) (hXL:L≤X) (hXH:X≤H)
    (hL:A*L^2+B*L+C≤R) (hH:A*H^2+B*H+C≤R) :
    A*X^2+B*X+C≤R := by
  by_cases he:L=H
  · have hx:X=L:=by linarith
    simpa only [hx] using hL
  have hLH:0<H-L:=by have:=lt_of_le_of_ne (hXL.trans hXH) he; linarith
  have hp:=mul_nonneg hA (mul_nonneg (sub_nonneg.mpr hXL) (sub_nonneg.mpr hXH))
  have heq:(H-X)*(A*L^2+B*L+C)+(X-L)*(A*H^2+B*H+C)-
      (H-L)*(A*X^2+B*X+C)=(H-L)*(A*((X-L)*(H-X))) := by ring
  have hlo:=mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr hXH)
  have hhi:=mul_le_mul_of_nonneg_left hH (sub_nonneg.mpr hXL)
  have hs:(H-L)*(A*X^2+B*X+C)≤(H-L)*R := by
    nlinarith [mul_nonneg hLH.le hp]
  exact (mul_le_mul_iff_right₀ hLH).mp (by simpa only [mul_comm] using hs)

lemma GSup_numerator {t:ℝ} (ht:0<t) (hr:t<1) :
    GSup t * UpperAlgebra.denominator (t^2) =
      UpperAlgebra.numerator (t^2) (8*(1-t^2)^2*f t) := by
  have hd:1-t^2≠0:=by nlinarith
  have hp:1+t^2≠0:=by positivity
  have hR:=f_relation (show t∈Ioo (-1:ℝ) 1 from ⟨by linarith,hr⟩)
  have he:fp t=(f t-1/(1-t^2)^3)/t := by
    apply (eq_div_iff ht.ne').mpr
    linear_combination hR
  rw [GSup,he]
  unfold qSup UpperAlgebra.denominator UpperAlgebra.numerator
  field_simp [hd,hp,ht.ne']
  ring

lemma GSup_far {t:ℝ} (hl:27/50≤t) (hr:t≤3/5) : GSup t≤c7 := by
  have ht:0<t:=by linarith
  have ht1:t<1:=by linarith
  have hd:0<1-t^2:=by nlinarith
  have hul:729/2500≤t^2:=by nlinarith
  have hur:t^2≤9/25:=by nlinarith
  obtain ⟨hL,hH⟩:=numerator_scaled_bounds ht.le ht1
  have hplo:=UpperAlgebra.bound_lo hul hur
  have hphi:=UpperAlgebra.bound_hi hul hur
  have identity (F:ℝ) : UpperAlgebra.numerator (t^2) F =
      (9*t^2*(1-t^2)*(1+t^2)^2+(1-6*t^2-3*(t^2)^2)^2)*F^2+
        (-16*(1-6*t^2-3*(t^2)^2)*(1+t^2))*F+64*(1+t^2)^2 := by
    unfold UpperAlgebra.numerator
    ring
  simp only [identity] at hplo hphi
  have hA:0≤9*t^2*(1-t^2)*(1+t^2)^2+(1-6*t^2-3*(t^2)^2)^2:=by positivity
  have hh:=quadratic_bound hA hL hH hplo hphi
  rw [←identity,←GSup_numerator ht ht1] at hh
  have hden:0<UpperAlgebra.denominator (t^2):=by unfold UpperAlgebra.denominator; positivity
  exact ((mul_le_mul_iff_left₀ hden).mp hh).trans c7_lower

/-- Exact replacement for the numerical supersolution slope plot, using the
rational τ=-2 Legendre solution and the rational angle 3/5. -/
theorem GSup_le_c7 {t:ℝ} (hl:t7≤t) (hr:t≤3/5) : GSup t≤c7 := by
  by_cases h:t≤27/50
  · exact GSup_near hl h
  · exact GSup_far (le_of_lt (lt_of_not_ge h)) hr

end Bernoulli.DeSilvaJerison
namespace Bernoulli.DeSilvaJerison

/-- The transverse unit-cylinder profile of the concrete upper barrier. -/
def capAmplitude : ℝ := -(10/17)*f (3/5)
def capRadius (s:ℝ) :ℝ := Real.sqrt (1+s^2)
def capAngle (s:ℝ) :ℝ := s/capRadius s
def capH (s:ℝ) :ℝ := capRadius s*f (capAngle s)+capAmplitude*(1+2*s^2)
def capHP (s:ℝ) :ℝ := capAngle s*f (capAngle s)+fp (capAngle s)/(capRadius s)^2+4*capAmplitude*s

def capP :ℝ := (3125/1024-13/2*capAmplitude)/(3125/1024-capAmplitude/8)
def capB :ℝ := (capP+3/50)/2

def capV (r:ℝ) :ℝ := 203/200-capB+capB*r^2-3/200*r^4

def capVP (r:ℝ) :ℝ := 2*capB*r-3/50*r^3

def capVPP (r:ℝ) :ℝ := 2*capB-9/50*r^2

def capY (r:ℝ) :ℝ := Real.sqrt (1+9/16*capP^2)*capV r/Real.sqrt (1+9/16*(capVP r)^2)

lemma capRadius_pos (s:ℝ) :0<capRadius s := Real.sqrt_pos.mpr (by positivity)
lemma capRadius_sq (s:ℝ) : (capRadius s)^2=1+s^2 := Real.sq_sqrt (by positivity)
lemma capAngle_mem (s:ℝ) : capAngle s∈Ioo (-1:ℝ) 1 := by
  have hr:=capRadius_pos s
  have hs:=capRadius_sq s
  constructor
  · rw [capAngle,lt_div_iff₀ hr]; nlinarith
  · rw [capAngle,div_lt_iff₀ hr]; nlinarith
lemma capAngle_d (s:ℝ) : 1-(capAngle s)^2=1/(capRadius s)^2 := by
  unfold capAngle
  field_simp [(capRadius_pos s).ne']
  nlinarith [capRadius_sq s]

lemma hasDerivAt_capRadius (s:ℝ) : HasDerivAt capRadius (s/capRadius s) s := by
  have hh:=(((hasDerivAt_const s (1:ℝ)).add ((hasDerivAt_id s).pow 2)).sqrt (by positivity : (1+s^2:ℝ)≠0))
  convert! hh using 1
  norm_num only [pow_one,id_eq]
  dsimp [capRadius]
  ring

lemma hasDerivAt_capAngle (s:ℝ) : HasDerivAt capAngle (1/(capRadius s)^3) s := by
  convert! (hasDerivAt_id s).div (hasDerivAt_capRadius s) (capRadius_pos s).ne' using 1
  simp only [id_eq,one_mul]
  field_simp [(capRadius_pos s).ne']
  nlinarith [capRadius_sq s]

lemma cap_f_relation (s:ℝ) : f (capAngle s)=capAngle s*fp (capAngle s)+(capRadius s)^6 := by
  have hh:=f_relation (capAngle_mem s)
  rw [capAngle_d] at hh
  have hr:capRadius s≠0:=(capRadius_pos s).ne'
  field_simp [hr] at hh
  linear_combination -hh

lemma hasDerivAt_capH (s:ℝ) : HasDerivAt capH (capHP s) s := by
  have hF:=(hasDerivAt_f (capAngle_mem s)).comp s (hasDerivAt_capAngle s)
  have hh:=((hasDerivAt_capRadius s).mul hF).add
    (((hasDerivAt_const s (1:ℝ)).add (((hasDerivAt_id s).pow 2).const_mul 2)).const_mul capAmplitude)
  convert! hh using 1
  simp only [Function.comp_apply,id_eq,capHP,capAngle]
  field_simp [(capRadius_pos s).ne']
  ring

lemma hasDerivAt_capHP (s:ℝ) : HasDerivAt capHP (-5*(capRadius s)^3+4*capAmplitude) s := by
  have hF:=(hasDerivAt_f (capAngle_mem s)).comp s (hasDerivAt_capAngle s)
  have hFP:=(hasDerivAt_fp (capAngle_mem s)).comp s (hasDerivAt_capAngle s)
  have hh:=(((hasDerivAt_capAngle s).mul hF).add
    (hFP.div ((hasDerivAt_capRadius s).pow 2) (pow_ne_zero 2 (capRadius_pos s).ne'))).add
      ((hasDerivAt_id s).const_mul (4*capAmplitude))
  convert! hh using 1
  simp only [Function.comp_apply,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,capAngle_d,cap_f_relation]
  unfold capAngle
  field_simp [(capRadius_pos s).ne']
  ring

lemma capH_even (s:ℝ) : capH (-s)=capH s := by
  simp only [capH,capRadius,neg_sq,capAngle,neg_div,f_neg]
lemma capHP_odd (s:ℝ) : capHP (-s)= -capHP s := by
  simp only [capHP,capRadius,neg_sq,capAngle,neg_div,f_neg,fp,A_neg]
  simp only [neg_div,neg_mul,mul_neg,neg_neg]
  ring
lemma capH_zero : capH 0=1+capAmplitude := by norm_num [capH,capRadius,capAngle,f_zero]
lemma capHP_zero : capHP 0=0 := by norm_num [capHP,capRadius,capAngle,fp_zero]
lemma capRadius_end : capRadius (3/4)=5/4 := by
  apply (sq_eq_sq₀ (capRadius_pos _).le (by norm_num)).mp
  rw [capRadius_sq]
  norm_num
lemma capAngle_end : capAngle (3/4)=3/5 := by rw [capAngle,capRadius_end]; norm_num
lemma capH_end : capH (3/4)=0 := by
  rw [capH,capRadius_end,capAngle_end,capAmplitude]
  ring
lemma capHP_end : capHP (3/4)=capAmplitude/6-3125/768 := by
  have hh:=f_relation (t:=3/5) (by norm_num)
  rw [capHP,capAngle_end,capRadius_end,capAmplitude]
  norm_num at hh ⊢
  linear_combination (16/15)*hh

lemma capAmplitude_bounds : 289237/1000000≤capAmplitude ∧ capAmplitude≤289241/1000000 := by
  have hA: (3/5:ℝ)*B 12 ((3/5:ℝ)^2)≤A (3/5) ∧
      A (3/5)≤(3/5:ℝ)*(B 12 ((3/5:ℝ)^2)+((3/5:ℝ)^2)^12/(1-(3/5:ℝ)^2)) :=
    A_series_bounds 12 (by norm_num) (by norm_num)
  dsimp [capAmplitude,f]
  norm_num [B,Finset.sum_range_succ] at hA ⊢
  constructor <;> linarith [hA.1,hA.2]
lemma capAmplitude_pos : 0<capAmplitude := by linarith [capAmplitude_bounds.1]
lemma capAmplitude_le : capAmplitude≤29/100 := by linarith [capAmplitude_bounds.2]

lemma capB_bounds : 2242/10000≤capB ∧ capB≤2243/10000 := by
  have hd:0<3125/1024-capAmplitude/8:=by linarith [capAmplitude_bounds.2]
  unfold capB capP
  constructor
  · apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (sub_le_iff_le_add).mp
    apply (le_div_iff₀ hd).mpr
    linarith [capAmplitude_bounds.2]
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (le_sub_iff_add_le).mp
    apply (div_le_iff₀ hd).mpr
    linarith [capAmplitude_bounds.1]

end Bernoulli.DeSilvaJerison

noncomputable section
namespace Bernoulli.DeSilvaJerison.CapSign
def flo (u:ℝ) :ℝ := (8+u*(-40+u*(40+u*(-8+u*((-8/7:ℝ)+u*((-8/21:ℝ)+u*((-40/231:ℝ)+u*((-460/33:ℝ)+u*(150/11:ℝ)))))))))
def polyK (u:ℝ) :ℝ := (431/200-673/250)*flo u/8+673/250-5*(1-u)+
  29/100*(1-u)*(4*(1-u)-4*(673/250)*u+431/200*(1+u))
def bern (x:ℝ) :ℝ :=
 (21201/20000:ℝ)*x^0*(1-x)^8 +
 (4795737/625000:ℝ)*x^1*(1-x)^7 +
 (1494048963/62500000:ℝ)*x^2*(1-x)^6 +
 (1300927593/31250000:ℝ)*x^3*(1-x)^5 +
 (480518798097/10937500000:ℝ)*x^4*(1-x)^4 +
 (1936812554529/68359375000:ℝ)*x^5*(1-x)^3 +
 (159112309786509/15039062500000:ℝ)*x^6*(1-x)^2 +
 (22814203319679/11749267578125:ℝ)*x^7*(1-x)^1 +
 (187538043427107/1879882812500000:ℝ)*x^8*(1-x)^0
lemma identity (x:ℝ) : -polyK (9/25*x)=bern x := by
  unfold polyK flo bern
  ring
lemma polyK_nonpos {u:ℝ} (hu:0≤u) (hu1:u≤9/25) : polyK u≤0 := by
  let x:ℝ := 25/9*u
  have hx:0≤x:=by dsimp [x]; positivity
  have hx1:x≤1:=by dsimp [x]; linarith
  have hh:0≤bern x := by
    have hy:0≤1-x:=sub_nonneg.mpr hx1
    unfold bern
    positivity
  have hi:=identity x
  have he:9/25*x=u:=by dsimp [x]; ring
  rw [he] at hi
  linarith
end Bernoulli.DeSilvaJerison.CapSign

namespace Bernoulli.DeSilvaJerison

lemma capRadius_one_le (s:ℝ) :1≤capRadius s := by
  have hp:=capRadius_pos s
  nlinarith [capRadius_sq s,sq_nonneg s]

lemma capHP_antitone : Antitone capHP := by
  apply antitone_of_deriv_nonpos (fun s=>(hasDerivAt_capHP s).differentiableAt)
  intro s
  rw [(hasDerivAt_capHP s).deriv]
  have hh:1≤(capRadius s)^3:=one_le_pow₀ (capRadius_one_le s)
  linarith [capAmplitude_le]

lemma capHP_nonpos {s:ℝ} (hs:0≤ s) :capHP s≤0 := by
  have hh:=capHP_antitone hs
  simpa only [capHP_zero] using hh

lemma capHP_le_linear {s:ℝ} (hs:0≤ s) : capHP s≤(-5+4*capAmplitude)*s := by
  let g:ℝ→ℝ:=fun t=>capHP t-(-5+4*capAmplitude)*t
  have hD (t:ℝ) :HasDerivAt g (-5*(capRadius t)^3+5) t := by
    convert! (hasDerivAt_capHP t).sub ((hasDerivAt_id t).const_mul (-5+4*capAmplitude)) using 1
    ring
  have hM:Antitone g := by
    apply antitone_of_deriv_nonpos (fun t=>(hD t).differentiableAt)
    intro t
    rw [(hD t).deriv]
    have hh:1≤(capRadius t)^3:=one_le_pow₀ (capRadius_one_le t)
    linarith
  have hh:=hM hs
  dsimp [g] at hh
  rw [capHP_zero] at hh
  linarith

lemma capH_antitone : AntitoneOn capH (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (0:ℝ))
  · exact fun s _=>(hasDerivAt_capH s).continuousAt.continuousWithinAt
  · exact fun s _=>(hasDerivAt_capH s).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [(hasDerivAt_capH s).deriv]
    exact capHP_nonpos (interior_subset hs)

lemma capH_nonneg {s:ℝ} (hs:|s|≤3/4) :0≤capH s := by
  have hh:=capH_antitone (show (|s|:ℝ)∈Set.Ici 0 from abs_nonneg s) (by norm_num : (3/4:ℝ)∈Set.Ici 0) hs
  rw [capH_end] at hh
  rcases le_total 0 s with hp|hn
  · simpa only [abs_of_nonneg hp] using hh
  · simpa only [abs_of_nonpos hn,capH_even] using hh

lemma capHPP_nonpos (s:ℝ) :-5*(capRadius s)^3+4*capAmplitude≤0 := by
  have hh:1≤(capRadius s)^3:=one_le_pow₀ (capRadius_one_le s)
  linarith [capAmplitude_le]

lemma capAngle_bounds {s:ℝ} (hs:0≤ s) (hs1:s≤3/4) : 0≤capAngle s ∧ capAngle s≤3/5 := by
  have hr:=capRadius_pos s
  constructor
  · exact div_nonneg hs hr.le
  · rw [capAngle,div_le_iff₀ hr]
    have hs2:s^2≤9/16:=by nlinarith
    nlinarith [capRadius_sq s]

lemma cap_flo_bound {t:ℝ} (ht:0≤t) (ht1:t≤3/5) : CapSign.flo (t^2)≤8*(1-t^2)^2*f t := by
  have hd:0<1-t^2:=by nlinarith
  have hl:=f_series_lower 6 ht (by linarith : t<1)
  have hi:CapSign.flo (t^2)/(8*(1-t^2)^2)=
      (8-25*t^2+15*(t^2)^2)/(8*(1-t^2)^2)-15/8*t^2*(B 6 (t^2)+(t^2)^6/(1-t^2)) := by
    unfold CapSign.flo B
    norm_num [Finset.sum_range_succ]
    field_simp [hd.ne']
    ring
  rw [←hi] at hl
  exact (div_le_iff₀ (by positivity)).mp hl |>.trans_eq (mul_comm _ _)

lemma cap_K_identity (s:ℝ) :
    (-5*(capRadius s)^3+4*capAmplitude-(673/250)*s*capHP s+(431/200)*capH s)/(capRadius s)^5=
      (431/200-673/250)*(1-(capAngle s)^2)^2*f (capAngle s)+673/250-5*(1-(capAngle s)^2)+
        capAmplitude/(capRadius s)^3*(4*(1-(capAngle s)^2)-4*(673/250)*(capAngle s)^2+431/200*(1+(capAngle s)^2)) := by
  rw [capHP,capH,capAngle_d,cap_f_relation]
  unfold capAngle
  field_simp [(capRadius_pos s).ne']
  have he:s^2=(capRadius s)^2-1:=by linarith [capRadius_sq s]
  have he3:s^3=s*((capRadius s)^2-1):=by linear_combination s*he
  ring_nf
  rw [he,he3]
  ring

theorem cap_K_nonpos {s:ℝ} (hs:|s|≤3/4) :
    -5*(capRadius s)^3+4*capAmplitude-(673/250)*s*capHP s+(431/200)*capH s≤0 := by
  suffices hp:∀t:ℝ, 0≤t → t≤3/4 →
      -5*(capRadius t)^3+4*capAmplitude-(673/250)*t*capHP t+(431/200)*capH t≤0 by
    rcases le_total 0 s with hpos|hneg
    · exact hp s hpos (by rw [abs_of_nonneg hpos] at hs; exact hs)
    · have hh:=hp (-s) (by linarith) (by rw [abs_of_nonpos hneg] at hs; exact hs)
      simpa only [capRadius,neg_sq,capHP_odd,capH_even,mul_neg,neg_mul,neg_neg] using hh
  intro s hs hs1
  obtain ⟨ht,ht1⟩:=capAngle_bounds hs hs1
  have hu:0≤(capAngle s)^2:=sq_nonneg _
  have hu1:(capAngle s)^2≤9/25:=by nlinarith
  have hd:0≤1-(capAngle s)^2:=by linarith
  have hB:0≤4*(1-(capAngle s)^2)-4*(673/250)*(capAngle s)^2+431/200*(1+(capAngle s)^2):=by linarith
  have hF:=cap_flo_bound ht ht1
  have hF':(431/200-673/250)*(1-(capAngle s)^2)^2*f (capAngle s)≤
      (431/200-673/250)*CapSign.flo ((capAngle s)^2)/8 := by nlinarith
  have hr:=capRadius_pos s
  have hr1:=capRadius_one_le s
  have hRa:capAmplitude/(capRadius s)^3≤29/100*(1-(capAngle s)^2) := by
    rw [capAngle_d]
    field_simp [hr.ne']
    nlinarith [capAmplitude_le]
  have hAB:=mul_le_mul_of_nonneg_right hRa hB
  have hp:=CapSign.polyK_nonpos hu hu1
  unfold CapSign.polyK at hp
  have hh:(-5*(capRadius s)^3+4*capAmplitude-(673/250)*s*capHP s+(431/200)*capH s)/(capRadius s)^5≤0 := by
    rw [cap_K_identity]
    linarith
  simpa only [zero_mul] using (div_le_iff₀ (pow_pos hr 5)).mp hh

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison

def capEta : ℝ := capP - (9/16)*capP*(capP-3/25)/(1+(9/16)*capP^2)
def capW (s : ℝ) : ℝ := (1-capEta)*capH s+(capP-1)*s*capHP s-3*capAmplitude*(1+2*s^2)
def capWP (s : ℝ) : ℝ := (capP-capEta)*capHP s+(capP-1)*s*(-5*(capRadius s)^3+4*capAmplitude)-12*capAmplitude*s
def capWPP (s : ℝ) : ℝ := (2*capP-capEta-1)*(-5*(capRadius s)^3+4*capAmplitude)+(capP-1)*(-15*s^2*capRadius s)-12*capAmplitude

lemma capP_bounds : 3884/10000≤capP ∧ capP≤3886/10000 := by
  have hh:=capB_bounds
  unfold capB at hh
  constructor <;> linarith [hh.1,hh.2]
lemma capEta_bounds : 1/3≤capEta ∧ capEta≤capP := by
  have hp:=capP_bounds
  have hq:0<1+(9/16)*capP^2:=by positivity
  have hpp:0≤capP*(capP-3/25):=mul_nonneg (by linarith [hp.1]) (by linarith [hp.1])
  have hprod:capP*(capP-3/25)≤(3886/10000)*(2686/10000):=by
    exact mul_le_mul hp.2 (by linarith [hp.2]) (by linarith [hp.1]) (by norm_num)
  have hsq:(3884/10000:ℝ)^2≤capP^2:=by nlinarith [hp.1]
  unfold capEta
  constructor
  · have hdelta : (9/16)*capP*(capP-3/25)/(1+(9/16)*capP^2)≤capP-1/3 := by
      apply (div_le_iff₀ hq).mpr
      have hh:=mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤9/16 from by norm_num)
      have ha:0≤capP-1/3:=by linarith [hp.1]
      have hb:((3884/10000:ℝ)-1/3)*(1+(9/16)*(3884/10000:ℝ)^2)≤(capP-1/3)*(1+(9/16)*capP^2):=
        mul_le_mul (by linarith [hp.1]) (by linarith) (by positivity) ha
      nlinarith
    linarith
  · exact sub_le_self _ (div_nonneg (by nlinarith) hq.le)

lemma capW_even (s : ℝ) : capW (-s)=capW s := by
  simp only [capW,capH_even,capHP_odd,neg_sq,mul_neg,neg_mul,neg_neg]
lemma capW_zero_nonpos : capW 0≤0 := by
  rw [capW,capH_zero,capHP_zero]
  norm_num
  have hprod:=mul_le_mul_of_nonneg_right capEta_bounds.1 capAmplitude_pos.le
  nlinarith [capAmplitude_bounds.1,capEta_bounds.1]
lemma capW_end : capW (3/4)=0 := by
  rw [capW,capH_end,capHP_end]
  simp only [mul_zero,zero_add]
  have hd:3125/1024-capAmplitude/8≠0:=ne_of_gt (by linarith [capAmplitude_le])
  have hp : capP*(3125/1024-capAmplitude/8)=3125/1024-13/2*capAmplitude := by
    rw [capP,div_mul_cancel₀ _ hd]
  nlinarith

lemma hasDerivAt_capW (s : ℝ) : HasDerivAt capW (capWP s) s := by
  have hh:=(((hasDerivAt_capH s).const_mul (1-capEta)).add
    (((hasDerivAt_id s).const_mul (capP-1)).mul (hasDerivAt_capHP s))).sub
    (((hasDerivAt_const s (1:ℝ)).add (((hasDerivAt_id s).pow 2).const_mul 2)).const_mul (3*capAmplitude))
  convert! hh using 1
  simp only [capWP,id_eq,Nat.cast_ofNat]
  ring
lemma hasDerivAt_capWP (s : ℝ) : HasDerivAt capWP (capWPP s) s := by
  have hR:=hasDerivAt_capRadius s
  have hH:HasDerivAt (fun t=>-5*(capRadius t)^3+4*capAmplitude) (-15*s*capRadius s) s := by
    convert! ((hR.pow 3).const_mul (-5)).add_const (4*capAmplitude) using 1
    norm_num only [Nat.reduceSub,Nat.cast_ofNat]
    field_simp [(capRadius_pos s).ne']
    ring
  have hh:=(((hasDerivAt_capHP s).const_mul (capP-capEta)).add
    (((hasDerivAt_id s).const_mul (capP-1)).mul hH)).sub ((hasDerivAt_id s).const_mul (12*capAmplitude))
  convert! hh using 1
  simp only [capWPP,id_eq]
  ring

lemma capRadius_cube_bound (s : ℝ) : (capRadius s)^3-1≤(3/2)*(capRadius s)*s^2 := by
  have hr:=capRadius_pos s
  have hh:=mul_nonneg (sq_nonneg (capRadius s-1)) (by linarith : 0≤capRadius s+2)
  nlinarith [capRadius_sq s, mul_nonneg (sq_nonneg (capRadius s-1)) hr.le]

lemma capW_radial_convex {s : ℝ} (hs : 0≤ s) : 0≤ s*capWPP s-capWP s := by
  have he:s*capWPP s-capWP s=(capP-capEta)*(s*(-5*(capRadius s)^3+4*capAmplitude)-capHP s)+
      15*(1-capP)*s^3*capRadius s := by unfold capWPP capWP; ring
  rw [he]
  have hc:0≤capP-capEta:=sub_nonneg.mpr capEta_bounds.2
  have hb:=mul_le_mul_of_nonneg_left (capHP_le_linear hs) hc
  have hR:=mul_le_mul_of_nonneg_left (capRadius_cube_bound s) (show 0≤5*(capP-capEta)*s by positivity)
  have hex:0≤(15*(1-capP)-(15/2)*(capP-capEta))*s^3*capRadius s := by
    have hh:0≤15*(1-capP)-(15/2)*(capP-capEta):=by linarith [capP_bounds.2,capEta_bounds.1]
    exact mul_nonneg (mul_nonneg hh (pow_nonneg hs 3)) (capRadius_pos s).le
  nlinarith

def capZ (q : ℝ) : ℝ := capW (Real.sqrt q)
def capZP (q : ℝ) : ℝ := capWP (Real.sqrt q)/(2*Real.sqrt q)
lemma hasDerivAt_capZ {q : ℝ} (hq : 0<q) : HasDerivAt capZ (capZP q) q := by
  convert! (hasDerivAt_capW (Real.sqrt q)).comp q (Real.hasDerivAt_sqrt hq.ne') using 1
  dsimp [capZP]
  ring
lemma hasDerivAt_capZP {q : ℝ} (hq : 0<q) :
    HasDerivAt capZP ((Real.sqrt q*capWPP (Real.sqrt q)-capWP (Real.sqrt q))/(4*(Real.sqrt q)^3)) q := by
  have hs:=Real.sqrt_pos.mpr hq
  convert! ((hasDerivAt_capWP (Real.sqrt q)).comp q (Real.hasDerivAt_sqrt hq.ne')).div
    ((Real.hasDerivAt_sqrt hq.ne').const_mul 2) (by positivity : 2*Real.sqrt q≠0) using 1
  simp only [Function.comp_apply]
  field_simp [hs.ne']
  ring
lemma capZ_convex : ConvexOn ℝ (Set.Icc 0 (9/16:ℝ)) capZ := by
  have hcont : Continuous capZ := (continuous_iff_continuousAt.mpr (fun s=>(hasDerivAt_capW s).continuousAt)).comp Real.continuous_sqrt
  have hp {q : ℝ} (hq : 0<q) : deriv capZ=ᶠ[𝓝 q] capZP := by
    filter_upwards [Ioi_mem_nhds hq] with t ht
    exact (hasDerivAt_capZ ht).deriv
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _) hcont.continuousOn
  · intro q hq
    rw [interior_Icc] at hq
    exact (hasDerivAt_capZ hq.1).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Icc] at hq
    exact ((hasDerivAt_capZP hq.1).congr_of_eventuallyEq (hp hq.1)).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Icc] at hq
    rw [Function.iterate_succ_apply',Function.iterate_one,(hp hq.1).deriv_eq,(hasDerivAt_capZP hq.1).deriv]
    exact div_nonneg (capW_radial_convex (Real.sqrt_nonneg q)) (by positivity)

/-- The exact jump sign at the cylindrical gluing interface of the outer
harmonic perturbation and the interior smooth cap. -/
theorem cap_interface_nonpos {s : ℝ} (hs : |s|≤3/4) : capW s≤0 := by
  have hsq : s^2∈Set.Icc (0:ℝ) (9/16) := ⟨sq_nonneg s,by nlinarith [sq_abs s,abs_nonneg s]⟩
  have hh:=capZ_convex.le_max_of_mem_Icc (by norm_num : (0:ℝ)∈Set.Icc 0 (9/16:ℝ))
    (by norm_num : (9/16:ℝ)∈Set.Icc 0 (9/16:ℝ)) hsq
  have hz0:capZ 0=capW 0:=by simp [capZ]
  have hz1:capZ (9/16)=0:=by
    rw [capZ,show Real.sqrt (9/16:ℝ)=3/4 by norm_num,capW_end]
  rw [hz0,hz1,max_eq_right capW_zero_nonpos] at hh
  dsimp [capZ] at hh
  rw [Real.sqrt_sq_eq_abs] at hh
  rcases le_total 0 s with hp|hn
  · simpa only [abs_of_nonneg hp] using hh
  · simpa only [abs_of_nonpos hn,capW_even] using hh

end Bernoulli.DeSilvaJerison
noncomputable section
namespace Bernoulli.DeSilvaJerison.CapAlgebra

def V (u b:ℝ) :ℝ := 203/200-b+b*u-3/200*u^2
def D (u b:ℝ) :ℝ := 2*b-3/50*u
def E (u b:ℝ) :ℝ := 2*b-9/50*u
def H (u b:ℝ) :ℝ := 1+9/16*u*(D u b)^2
def MN (u b:ℝ) :ℝ := E u b*(1-9/16*u*(D u b)^2)+5*D u b*H u b
def NN (u b:ℝ) :ℝ := MN u b*H u b-
  9/16*V u b*((E u b)^2-9/25*u*D u b+5*D u b*E u b)*H u b+
  3*(9/16)^2*V u b*u*(D u b)^2*(E u b)^2
def Mlo_0 (z:ℝ) :ℝ :=
 (3363/1250:ℝ)*z^0*(1-z)^3 +
 (20181/2500:ℝ)*z^1*(1-z)^2 +
 (5046/625:ℝ)*z^2*(1-z)^1 +
 (6729/2500:ℝ)*z^3*(1-z)^0
lemma Mlo_0_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mlo_0 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mlo_0
  positivity
def Mlo_1 (z:ℝ) :ℝ :=
 (655278251049/250000000000:ℝ)*z^0*(1-z)^3 +
 (3932303435601/500000000000:ℝ)*z^1*(1-z)^2 +
 (7865874760083/1000000000000:ℝ)*z^2*(1-z)^1 +
 (5244761786163/2000000000000:ℝ)*z^3*(1-z)^0
lemma Mlo_1_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mlo_1 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mlo_1
  positivity
def Mlo_2 (z:ℝ) :ℝ :=
 (79391132481/31250000000:ℝ)*z^0*(1-z)^3 +
 (1905718586601/250000000000:ℝ)*z^1*(1-z)^2 +
 (1906050008229/250000000000:ℝ)*z^2*(1-z)^1 +
 (2541841925913/1000000000000:ℝ)*z^3*(1-z)^0
lemma Mlo_2_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mlo_2 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mlo_2
  positivity
def Mlo_3 (z:ℝ) :ℝ :=
 (612606431397/250000000000:ℝ)*z^0*(1-z)^3 +
 (3676325647803/500000000000:ℝ)*z^1*(1-z)^2 +
 (7354025498499/1000000000000:ℝ)*z^2*(1-z)^1 +
 (4903599856989/2000000000000:ℝ)*z^3*(1-z)^0
lemma Mlo_3_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mlo_3 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mlo_3
  positivity
def Mlo_4 (z:ℝ) :ℝ :=
 (73512952587/31250000000:ℝ)*z^0*(1-z)^3 +
 (882332198601/125000000000:ℝ)*z^1*(1-z)^2 +
 (220627244901/31250000000:ℝ)*z^2*(1-z)^1 +
 (1176914365413/500000000000:ℝ)*z^3*(1-z)^0
lemma Mlo_4_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mlo_4 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mlo_4
  positivity
def bern_Mlo (u z:ℝ) :ℝ :=
 1*Mlo_0 z*u^0*(1-u)^4 +
 4*Mlo_1 z*u^1*(1-u)^3 +
 6*Mlo_2 z*u^2*(1-u)^2 +
 4*Mlo_3 z*u^3*(1-u)^1 +
 1*Mlo_4 z*u^4*(1-u)^0
lemma identity_Mlo (u z:ℝ) :
    (let b:ℝ := 2242/10000+z/10000; MN u b)=bern_Mlo u z := by
  dsimp
  simp only [MN, H,D, E, bern_Mlo, Mlo_0, Mlo_1, Mlo_2, Mlo_3, Mlo_4]
  ring
lemma Mlo_nonneg {u b:ℝ} (hu:0≤u) (hu1:u≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0≤MN u b := by
  let z:ℝ := (b-2242/10000)*10000
  have hz:0≤z:=by dsimp [z]; linarith
  have hz1:z≤1:=by dsimp [z]; linarith
  have he:2242/10000+z/10000=b:=by dsimp [z]; ring
  have hi:=identity_Mlo u z
  dsimp only at hi
  rw [he] at hi
  rw [hi]
  have hx:0≤1-u:=sub_nonneg.mpr hu1
  have h0:= Mlo_0_nonneg hz hz1
  have h1:= Mlo_1_nonneg hz hz1
  have h2:= Mlo_2_nonneg hz hz1
  have h3:= Mlo_3_nonneg hz hz1
  have h4:= Mlo_4_nonneg hz hz1
  unfold bern_Mlo
  positivity
def Mhi_0 (z:ℝ) :ℝ :=
 (1/625:ℝ)*z^0*(1-z)^3 +
 (9/2500:ℝ)*z^1*(1-z)^2 +
 (3/1250:ℝ)*z^2*(1-z)^1 +
 (1/2500:ℝ)*z^3*(1-z)^0
lemma Mhi_0_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mhi_0 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mhi_0
  positivity
def Mhi_1 (z:ℝ) :ℝ :=
 (73500870587/500000000000:ℝ)*z^0*(1-z)^3 +
 (219902631939/500000000000:ℝ)*z^1*(1-z)^2 +
 (877210578219/2000000000000:ℝ)*z^2*(1-z)^1 +
 (145801766401/1000000000000:ℝ)*z^3*(1-z)^0
lemma Mhi_1_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mhi_1 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mhi_1
  positivity
def Mhi_2 (z:ℝ) :ℝ :=
 (72533364337/250000000000:ℝ)*z^0*(1-z)^3 +
 (217301121189/250000000000:ℝ)*z^1*(1-z)^2 +
 (868008569469/1000000000000:ℝ)*z^2*(1-z)^1 +
 (72234385513/250000000000:ℝ)*z^3*(1-z)^0
lemma Mhi_2_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mhi_2 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mhi_2
  positivity
def Mhi_3 (z:ℝ) :ℝ :=
 (215270976761/500000000000:ℝ)*z^0*(1-z)^3 +
 (645218633817/500000000000:ℝ)*z^1*(1-z)^2 +
 (2578497272157/2000000000000:ℝ)*z^2*(1-z)^1 +
 (429353321953/1000000000000:ℝ)*z^3*(1-z)^0
lemma Mhi_3_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mhi_3 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mhi_3
  positivity
def Mhi_4 (z:ℝ) :ℝ :=
 (71002129337/125000000000:ℝ)*z^0*(1-z)^3 +
 (212859027189/125000000000:ℝ)*z^1*(1-z)^2 +
 (850846641969/500000000000:ℝ)*z^2*(1-z)^1 +
 (35427381319/62500000000:ℝ)*z^3*(1-z)^0
lemma Mhi_4_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mhi_4 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mhi_4
  positivity
def bern_Mhi (u z:ℝ) :ℝ :=
 1*Mhi_0 z*u^0*(1-u)^4 +
 4*Mhi_1 z*u^1*(1-u)^3 +
 6*Mhi_2 z*u^2*(1-u)^2 +
 4*Mhi_3 z*u^3*(1-u)^1 +
 1*Mhi_4 z*u^4*(1-u)^0
lemma identity_Mhi (u z:ℝ) :
    (let b:ℝ := 2242/10000+z/10000; 673/250*H u b-MN u b)=bern_Mhi u z := by
  dsimp
  simp only [MN, H,D, E, bern_Mhi, Mhi_0, Mhi_1, Mhi_2, Mhi_3, Mhi_4]
  ring
lemma Mhi_nonneg {u b:ℝ} (hu:0≤u) (hu1:u≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0≤673/250*H u b-MN u b := by
  let z:ℝ := (b-2242/10000)*10000
  have hz:0≤z:=by dsimp [z]; linarith
  have hz1:z≤1:=by dsimp [z]; linarith
  have he:2242/10000+z/10000=b:=by dsimp [z]; ring
  have hi:=identity_Mhi u z
  dsimp only at hi
  rw [he] at hi
  rw [hi]
  have hx:0≤1-u:=sub_nonneg.mpr hu1
  have h0:= Mhi_0_nonneg hz hz1
  have h1:= Mhi_1_nonneg hz hz1
  have h2:= Mhi_2_nonneg hz hz1
  have h3:= Mhi_3_nonneg hz hz1
  have h4:= Mhi_4_nonneg hz hz1
  unfold bern_Mhi
  positivity
def Nlo_0 (z:ℝ) :ℝ :=
 (269221760061/125000000000:ℝ)*z^0*(1-z)^5 +
 (5384829779091/500000000000:ℝ)*z^1*(1-z)^4 +
 (2692612172703/125000000000:ℝ)*z^2*(1-z)^3 +
 (43084951201347/2000000000000:ℝ)*z^3*(1-z)^2 +
 (10772026886763/1000000000000:ℝ)*z^4*(1-z)^1 +
 (4309126380039/2000000000000:ℝ)*z^5*(1-z)^0
lemma Nlo_0_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_0 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_0
  positivity
def Nlo_1 (z:ℝ) :ℝ :=
 (382600657861063335909/175000000000000000000:ℝ)*z^0*(1-z)^5 +
 (1530524055108837852339/140000000000000000000:ℝ)*z^1*(1-z)^4 +
 (382661369286668105259/17500000000000000000:ℝ)*z^2*(1-z)^3 +
 (6123067590235820584581/280000000000000000000:ℝ)*z^3*(1-z)^2 +
 (6123553265387536509219/560000000000000000000:ℝ)*z^4*(1-z)^1 +
 (24496155736186519478199/11200000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nlo_1_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_1 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_1
  positivity
def Nlo_2 (z:ℝ) :ℝ :=
 (775057445541430053771/350000000000000000000:ℝ)*z^0*(1-z)^5 +
 (1550247224503752406083/140000000000000000000:ℝ)*z^1*(1-z)^4 +
 (3100759115968495184859/140000000000000000000:ℝ)*z^2*(1-z)^3 +
 (6202047566103361871307/280000000000000000000:ℝ)*z^3*(1-z)^2 +
 (12405153801040206854811/1120000000000000000000:ℝ)*z^4*(1-z)^1 +
 (24812424940772777719203/11200000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nlo_2_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_2 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_2
  positivity
def Nlo_3 (z:ℝ) :ℝ :=
 (48958478704618351989/21875000000000000000:ℝ)*z^0*(1-z)^5 +
 (783407241197278452747/70000000000000000000:ℝ)*z^1*(1-z)^4 +
 (391739412012590216571/17500000000000000000:ℝ)*z^2*(1-z)^3 +
 (447743090147723034423/20000000000000000000:ℝ)*z^3*(1-z)^2 +
 (783621992398198851/70000000000000000:ℝ)*z^4*(1-z)^1 +
 (12539097247122349634271/5600000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nlo_3_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_3 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_3
  positivity
def Nlo_4 (z:ℝ) :ℝ :=
 (394997188657314790971/175000000000000000000:ℝ)*z^0*(1-z)^5 +
 (790071314230783404417/70000000000000000000:ℝ)*z^1*(1-z)^4 +
 (1580296505902245781203/70000000000000000000:ℝ)*z^2*(1-z)^3 +
 (632180154781400295717/28000000000000000000:ℝ)*z^3*(1-z)^2 +
 (6322417086470145808443/560000000000000000000:ℝ)*z^4*(1-z)^1 +
 (12646065279172462395873/5600000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nlo_4_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_4 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_4
  positivity
def Nlo_5 (z:ℝ) :ℝ :=
 (79500176095315489509/35000000000000000000:ℝ)*z^0*(1-z)^5 +
 (318033589904376947673/28000000000000000000:ℝ)*z^1*(1-z)^4 +
 (79516619129149257177/3500000000000000000:ℝ)*z^2*(1-z)^3 +
 (1272397456873777666359/56000000000000000000:ℝ)*z^3*(1-z)^2 +
 (254505802408353089607/22400000000000000000:ℝ)*z^4*(1-z)^1 +
 (5090642286289762414869/2240000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nlo_5_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_5 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_5
  positivity
def Nlo_6 (z:ℝ) :ℝ :=
 (798333880165936252233/350000000000000000000:ℝ)*z^0*(1-z)^5 +
 (1596842554436556680349/140000000000000000000:ℝ)*z^1*(1-z)^4 +
 (3194034711701294217297/140000000000000000000:ℝ)*z^2*(1-z)^3 +
 (6388768658308765709541/280000000000000000000:ℝ)*z^3*(1-z)^2 +
 (1825562263564842891039/160000000000000000000:ℝ)*z^4*(1-z)^1 +
 (25560668863677337021869/11200000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nlo_6_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_6 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_6
  positivity
def Nlo_7 (z:ℝ) :ℝ :=
 (14285237132421382131/6250000000000000000:ℝ)*z^0*(1-z)^5 +
 (28573776877165480983/2500000000000000000:ℝ)*z^1*(1-z)^4 +
 (57154159307184777219/2500000000000000000:ℝ)*z^2*(1-z)^3 +
 (114321530376744764967/5000000000000000000:ℝ)*z^3*(1-z)^2 +
 (228669485592076793331/20000000000000000000:ℝ)*z^4*(1-z)^1 +
 (457391823490005261783/200000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nlo_7_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_7 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_7
  positivity
def bern_Nlo (u z:ℝ) :ℝ :=
 1*Nlo_0 z*u^0*(1-u)^7 +
 7*Nlo_1 z*u^1*(1-u)^6 +
 21*Nlo_2 z*u^2*(1-u)^5 +
 35*Nlo_3 z*u^3*(1-u)^4 +
 35*Nlo_4 z*u^4*(1-u)^3 +
 21*Nlo_5 z*u^5*(1-u)^2 +
 7*Nlo_6 z*u^6*(1-u)^1 +
 1*Nlo_7 z*u^7*(1-u)^0
lemma identity_Nlo (u z:ℝ) :
    (let b:ℝ := 2242/10000+z/10000; NN u b)=bern_Nlo u z := by
  dsimp
  simp only [NN, MN, H, V, D, E, bern_Nlo, Nlo_0, Nlo_1, Nlo_2, Nlo_3, Nlo_4, Nlo_5, Nlo_6, Nlo_7]
  ring
lemma Nlo_nonneg {u b:ℝ} (hu:0≤u) (hu1:u≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0≤NN u b := by
  let z:ℝ := (b-2242/10000)*10000
  have hz:0≤z:=by dsimp [z]; linarith
  have hz1:z≤1:=by dsimp [z]; linarith
  have he:2242/10000+z/10000=b:=by dsimp [z]; ring
  have hi:=identity_Nlo u z
  dsimp only at hi
  rw [he] at hi
  rw [hi]
  have hx:0≤1-u:=sub_nonneg.mpr hu1
  have h0:= Nlo_0_nonneg hz hz1
  have h1:= Nlo_1_nonneg hz hz1
  have h2:= Nlo_2_nonneg hz hz1
  have h3:= Nlo_3_nonneg hz hz1
  have h4:= Nlo_4_nonneg hz hz1
  have h5:= Nlo_5_nonneg hz hz1
  have h6:= Nlo_6_nonneg hz hz1
  have h7:= Nlo_7_nonneg hz hz1
  unfold bern_Nlo
  positivity
def Nhi_0 (z:ℝ) :ℝ :=
 (153239939/125000000000:ℝ)*z^0*(1-z)^5 +
 (2670220909/500000000000:ℝ)*z^1*(1-z)^4 +
 (1137827297/125000000000:ℝ)*z^2*(1-z)^3 +
 (15048798653/2000000000000:ℝ)*z^3*(1-z)^2 +
 (2973113237/1000000000000:ℝ)*z^4*(1-z)^1 +
 (873619961/2000000000000:ℝ)*z^5*(1-z)^0
lemma Nhi_0_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_0 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_0
  positivity
def Nhi_1 (z:ℝ) :ℝ :=
 (6710618236436664091/175000000000000000000:ℝ)*z^0*(1-z)^5 +
 (26729745999162147661/140000000000000000000:ℝ)*z^1*(1-z)^4 +
 (950607916038484963/2500000000000000000:ℝ)*z^2*(1-z)^3 +
 (106017199577179415419/280000000000000000000:ℝ)*z^3*(1-z)^2 +
 (105566322934463490781/560000000000000000000:ℝ)*z^4*(1-z)^1 +
 (420461826653480521801/11200000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nhi_1_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_1 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_1
  positivity
def Nhi_2 (z:ℝ) :ℝ :=
 (13111446287006550577/175000000000000000000:ℝ)*z^0*(1-z)^5 +
 (52330785122706030907/140000000000000000000:ℝ)*z^1*(1-z)^4 +
 (26107893543479728289/35000000000000000000:ℝ)*z^2*(1-z)^3 +
 (208403164157297163073/280000000000000000000:ℝ)*z^3*(1-z)^2 +
 (207943187913353315467/560000000000000000000:ℝ)*z^4*(1-z)^1 +
 (829932878440629602647/11200000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nhi_2_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_2 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_2
  positivity
def Nhi_3 (z:ℝ) :ℝ :=
 (38827439179978619951/350000000000000000000:ℝ)*z^0*(1-z)^5 +
 (19384386394708716919/35000000000000000000:ℝ)*z^1*(1-z)^4 +
 (154840428418693554377/140000000000000000000:ℝ)*z^2*(1-z)^3 +
 (154605768499513427459/140000000000000000000:ℝ)*z^3*(1-z)^2 +
 (123496889117325415927/224000000000000000000:ℝ)*z^4*(1-z)^1 +
 (77068228553325460813/700000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nhi_3_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_3 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_3
  positivity
def Nhi_4 (z:ℝ) :ℝ :=
 (800715769361209697/5468750000000000000:ℝ)*z^0*(1-z)^5 +
 (51185932986797940953/70000000000000000000:ℝ)*z^1*(1-z)^4 +
 (25563028582094833723/17500000000000000000:ℝ)*z^2*(1-z)^3 +
 (40852945416226297891/28000000000000000000:ℝ)*z^3*(1-z)^2 +
 (51006306804067794449/70000000000000000000:ℝ)*z^4*(1-z)^1 +
 (815142916232554221677/5600000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nhi_4_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_4 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_4
  positivity
def Nhi_5 (z:ℝ) :ℝ :=
 (1587610118570041229/8750000000000000000:ℝ)*z^0*(1-z)^5 +
 (3625329355203510101/4000000000000000000:ℝ)*z^1*(1-z)^4 +
 (25352849141682898457/14000000000000000000:ℝ)*z^2*(1-z)^3 +
 (101313571449733664801/56000000000000000000:ℝ)*z^3*(1-z)^2 +
 (10121574659285550611/11200000000000000000:ℝ)*z^4*(1-z)^1 +
 (404471687976992180831/2240000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nhi_5_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_5 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_5
  positivity
def Nhi_6 (z:ℝ) :ℝ :=
 (37821484030869718321/175000000000000000000:ℝ)*z^0*(1-z)^5 +
 (151160996163694918501/140000000000000000000:ℝ)*z^1*(1-z)^4 +
 (10788289715972042801/5000000000000000000:ℝ)*z^2*(1-z)^3 +
 (603644462802436405159/280000000000000000000:ℝ)*z^3*(1-z)^2 +
 (603144700768341858451/560000000000000000000:ℝ)*z^4*(1-z)^1 +
 (2410579751926825325881/11200000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nhi_6_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_6 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_6
  positivity
def Nhi_7 (z:ℝ) :ℝ :=
 (12530356731138217727/50000000000000000000:ℝ)*z^0*(1-z)^5 +
 (12521232400567437053/10000000000000000000:ℝ)*z^1*(1-z)^4 +
 (50048432087552403293/20000000000000000000:ℝ)*z^2*(1-z)^3 +
 (12502983594891765863/5000000000000000000:ℝ)*z^3*(1-z)^2 +
 (199901745909919602587/160000000000000000000:ℝ)*z^4*(1-z)^1 +
 (199755753521828125643/800000000000000000000:ℝ)*z^5*(1-z)^0
lemma Nhi_7_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_7 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_7
  positivity
def bern_Nhi (u z:ℝ) :ℝ :=
 1*Nhi_0 z*u^0*(1-u)^7 +
 7*Nhi_1 z*u^1*(1-u)^6 +
 21*Nhi_2 z*u^2*(1-u)^5 +
 35*Nhi_3 z*u^3*(1-u)^4 +
 35*Nhi_4 z*u^4*(1-u)^3 +
 21*Nhi_5 z*u^5*(1-u)^2 +
 7*Nhi_6 z*u^6*(1-u)^1 +
 1*Nhi_7 z*u^7*(1-u)^0
lemma identity_Nhi (u z:ℝ) :
    (let b:ℝ := 2242/10000+z/10000; 431/200*(H u b)^2-NN u b)=bern_Nhi u z := by
  dsimp
  simp only [NN, MN, H, V, D, E, bern_Nhi, Nhi_0, Nhi_1, Nhi_2, Nhi_3, Nhi_4, Nhi_5, Nhi_6, Nhi_7]
  ring
lemma Nhi_nonneg {u b:ℝ} (hu:0≤u) (hu1:u≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0≤431/200*(H u b)^2-NN u b := by
  let z:ℝ := (b-2242/10000)*10000
  have hz:0≤z:=by dsimp [z]; linarith
  have hz1:z≤1:=by dsimp [z]; linarith
  have he:2242/10000+z/10000=b:=by dsimp [z]; ring
  have hi:=identity_Nhi u z
  dsimp only at hi
  rw [he] at hi
  rw [hi]
  have hx:0≤1-u:=sub_nonneg.mpr hu1
  have h0:= Nhi_0_nonneg hz hz1
  have h1:= Nhi_1_nonneg hz hz1
  have h2:= Nhi_2_nonneg hz hz1
  have h3:= Nhi_3_nonneg hz hz1
  have h4:= Nhi_4_nonneg hz hz1
  have h5:= Nhi_5_nonneg hz hz1
  have h6:= Nhi_6_nonneg hz hz1
  have h7:= Nhi_7_nonneg hz hz1
  unfold bern_Nhi
  positivity

lemma H_pos {u b:ℝ} (hu:0≤u) : 0<H u b := by unfold H; positivity
lemma coeff_bounds {u b:ℝ} (hu:0≤u) (hu1:u≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0≤MN u b/H u b ∧ MN u b/H u b≤673/250 ∧
      0≤NN u b/(H u b)^2 ∧ NN u b/(H u b)^2≤431/200 := by
  have hh:=H_pos (b:=b) hu
  refine ⟨div_nonneg (Mlo_nonneg hu hu1 hb hb1) hh.le,?_,
    div_nonneg (Nlo_nonneg hu hu1 hb hb1) (sq_nonneg _),?_⟩
  · rw [div_le_iff₀ hh]
    linarith [Mhi_nonneg hu hu1 hb hb1]
  · rw [div_le_iff₀ (sq_pos_of_pos hh)]
    linarith [Nhi_nonneg hu hu1 hb hb1]
end Bernoulli.DeSilvaJerison.CapAlgebra

end
end
end
end

end OAI
