import OAI.Geometry.Convex.GeneralMahler.Scalar.Regular
import OAI.Geometry.Convex.GeneralMahler.Scalar.Pass

namespace OAI
/-! Circular profile and layer bound envelopes. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Tag Grid Jet Profile Layers Cert Cert.IV
noncomputable section
abbrev lc:=liftF uc
abbrev ls:=liftF us
lemma lc_e (x) : lc x= r * Real.cos (omegaP*x):= by unfold lc liftF uc; rw [x_ang]
lemma ls_e (x) : ls x= r * Real.sin (omegaP*x):= by unfold ls liftF us; rw [x_ang]
lemma lcsq (x): lc x^2+ ls x^2 = r^2 := by
  rw [lc_e,ls_e]; have h:= Real.sin_sq_add_cos_sq (omegaP*x)
  linear_combination r^2*h
lemma dlc (x:ℝ): HasDerivAt lc (-omegaP*ls x) x:= by
  rw [funext lc_e,ls_e]
  convert ((Real.hasDerivAt_cos _).comp x ((hasDerivAt_id' x).const_mul omegaP)).const_mul r using 1
  all_goals first|rfl|ring
lemma dls (x:ℝ):HasDerivAt ls (omegaP*lc x) x:=by
  rw [funext ls_e,lc_e]
  convert ((Real.hasDerivAt_sin _).comp x ((hasDerivAt_id' x).const_mul omegaP)).const_mul r using 1
  all_goals first|rfl|ring
def ca (x:ℝ):=2+omegaP^2*(ast x)⁻¹^2
def cb1 (x:ℝ):=(1+(ast x)⁻¹^2)*omegaP* thR x
lemma NC_c (x:ℝ): N2 uc (xs x)=ca x*lc x-cb1 x*ls x := by
  have he := (SCov uc ucs_reg.1 x).2
  have hd : DotF uc = fun x=> -omegaP*ls x := funext fun x=> (dlc x).deriv
  have hh : DDot uc x = -omegaP*(omegaP*lc x):= by rw [DDot, hd]; exact ((dls x).const_mul _).deriv
  rw [he,NNf,hh,hd]
  change 2*lc x+_ - _=_
  unfold ca cb1; ring
lemma NC_s (x:ℝ): N2 us (xs x)=ca x*ls x+cb1 x*lc x := by
  have he := (SCov us ucs_reg.2 x).2
  have hd : DotF us = fun x=> omegaP*lc x:= funext fun x=>(dls x).deriv
  have hh : DDot us x= omegaP*(-omegaP*ls x):= by rw [DDot,hd]; exact ((dlc x).const_mul _).deriv
  rw [he,NNf,hh,hd]
  change 2*ls x+_ - _=_
  unfold ca cb1; ring

def ro2 (x:ℝ):=r^2*(ca x^2+cb1 x^2)
lemma nr2 (x): ro2 x=N2 uc (xs x)^2+ N2 us (xs x)^2:= by
  rw [NC_c,NC_s,ro2, ← lcsq x]; ring
def aY (x:ℝ):=(1-x)/sb^2
def rPoly (x:ℝ):=
  r^2*((2+omegaP^2*aY x)^2+(1+aY x)^2*omegaP^2*x)
lemma uA (x:ℝ): (ast x)⁻¹^2=aY (thR x^2) := by
  have hi : ast x ^2= xs x^2+sb^2 := by
    unfold ast xs; linear_combination sb^2*Real.cosh_sq_sub_sinh_sq x
  unfold aY thR
  have hp:=ap x
  field_simp [hsb.ne']
  linarith
lemma rx_eq (x:ℝ): ro2 x=rPoly (thR x^2):=by unfold ro2 ca cb1; rw [uA]; unfold rPoly; ring
lemma ri0 (x:ℝ): thR x^2∈Icc (0:ℝ) 1 := by
  have hi:= uA x; unfold aY at hi
  refine ⟨sq_nonneg _,?_⟩
  have hh:0≤ (1-thR x^2)/sb^2:=hi ▸ sq_nonneg _
  rw [le_div_iff₀ (sq_pos_of_pos hsb)] at hh; linarith
lemma rPolyMono : MonotoneOn rPoly (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  unfold rPoly
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  set a:=aY x
  set b:=aY y
  have he : a-b=(y-x)/sb^2:=by dsimp [a,b,aY];ring
  have hah (x:ℝ) (hx:x∈Icc (0:ℝ) 1): 0≤aY x ∧ aY x≤1/sb^2 := by
    have H₁ : 0 ≤ x:=hx.1;have H₂:x≤1:=hx.2
    unfold aY; exact ⟨div_nonneg (by linarith) (by positivity), div_le_div_of_nonneg_right (by linarith) (by positivity)⟩
  obtain ⟨ha,hb⟩:=hah x hx; obtain ⟨hc,hd⟩:=hah y hy
  change 0≤a at ha;change a ≤ _ at hb
  change 0≤b at hc;change b ≤ _ at hd
  have hh : 0 ≤ (1+b)^2- x*(2+a+b)/sb^2- (4+omegaP^2*(a+b))/sb^2 := by
    have hh1:0≤x:= hx.1; have hh2:x≤1:= hx.2
    unfold sb omegaP at *
    have hi:= mul_nonneg (show 0≤(1-x) by linarith) (show 0≤2+a+b by linarith)
    norm_num at *
    nlinarith
  have H:=mul_nonneg (mul_nonneg (show 0≤y-x by linarith) (sq_nonneg omegaP)) hh
  rw [← sub_nonneg]
  apply H.trans_eq
  rw [show y = x + sb^2*(a-b) from by field_simp [hsb.ne'] at he; linarith]
  field_simp [hsb.ne']; ring
lemma th_m: Monotone thR:= by
  intro x y h
  unfold thR xs ast
  have hp (y:ℝ):0 < sb*cosh y:= ap y
  rw [div_le_div_iff₀ (hp _) (hp _)]
  have he : 0 ≤ sinh (y-x):=Real.sinh_nonneg_iff.mpr (by linarith)
  rw [Real.sinh_sub] at he
  apply sub_nonneg.mp
  have hi:=mul_nonneg (sq_nonneg sb) he
  linarith
lemma r_monoP : MonotoneOn ro2 (Ici 0):= by
  intro x hx y hy h
  rw [rx_eq,rx_eq]; apply rPolyMono (ri0 _) (ri0 _); gcongr
  · apply le_trans _ (th_m hx); simp [thR,xs]
  apply th_m h
lemma ro2_neg (x):ro2 (-x)=ro2 x:=by rw [rx_eq,rx_eq,th_eq,th_eq];simp

end
def omegaB:=bd 46000
def rBox (A:Row0):IV:=
  let p:=omegaB
  let y:=A.X/A.T
  let h:=IV.sq (A.T)⁻¹
  IV.sq (bd 2200)*(IV.sq (2+IV.sq p*h)+IV.sq ((1+h)*p*y))
lemma mroB {t:ℝ}{A:Row0} (h:Row0.At t A): ro2 t∈rBox A:=by
  have hp:omegaP∈omegaB := by unfold omegaB; convert mbd 46000; norm_num [omegaP]
  have hv:Profile.r∈bd 2200:=by convert mbd 2200; norm_num [r]
  have h₁:=msq (minv h.T)
  exact mmul (msq hv)
    (madd (msq (madd mtwo (mmul (msq hp) h₁))) (msq (mmul (mmul (madd mo h₁) hp)
      (mdiv h.X h.T))))
noncomputable def rPanel (k:ℕ):ℝ:= ((panel k).rh:ℝ)/10000
-- finite arithmetic at upper cells
def testPn (k:Nat):Bool:=
  if (panel k).hi < 720 then LeB (rBox (pG (panel k).hi)) (sq (bd (panel k).rh))
  else true
lemma pnT : (List.range 9).all testPn=true := by decide +kernel
lemma rp_pos (k:Nat) (h:k≤8):0 ≤ rPanel k:=by
  interval_cases k <;> norm_num [rPanel,panel,pan]
lemma rp_val (k:Nat) (h:k≤8) (x:ℝ) (hx:(panel k).hi < 720→ |x|≤nd (panel k).hi):
    ro2 x ≤ rPanel k^2 := by
  have he :ro2 x=ro2 |x|:=by rcases le_total 0 x with h|h; rw [abs_of_nonneg h]; rw [abs_of_nonpos h,ro2_neg]
  rw [he]
  by_cases hh:(panel k).hi<720
  · have hq:=List.all_eq_true.mp pnT k (List.mem_range.mpr (by omega))
    rw [testPn,ite_eq_left hh] at hq
    have hj:= r_monoP (abs_nonneg x) (n_nn _) (hx hh)
    exact hj.trans (mle (mroB (pGa _)) (msq (mbd _)) hq)
  have hu:k=8 := by interval_cases k <;> norm_num [panel,pan] at *
  rw [rx_eq]
  have hr:=ri0 |x|
  apply (rPolyMono hr (show 1∈Icc (0:ℝ) 1 from ⟨by norm_num,le_rfl⟩) hr.2).trans
  subst k; norm_num [rPoly,rPanel,r,omegaP,aY,panel,pan]
end GeneralMahler.SCal

end OAI
