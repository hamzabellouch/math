import OAI.Geometry.Convex.GeneralMahler.Scalar.Universal

namespace OAI
/-! Finite-area bound and infinite tail for K. -/
open MeasureTheory Set Filter Real
open scoped Topology Interval
namespace GeneralMahler.SCal
open Grid Tag Jet Profile Cert Cert.IV Nodes
noncomputable section
def KP0 (x:ℝ):=max 0 (Kp x)
lemma posKP (x:ℝ):0 ≤ KP0 x:=le_max_left ..
lemma contKP: Continuous KP0:= continuous_const.max testK.cont
def ikp (x:ℝ):=∫ y in (0:ℝ)..x,KP0 y
lemma idk0 (x):HasDerivAt ikp (KP0 x) x := intervalIntegral.integral_hasDerivAt_right
  (contKP.intervalIntegrable ..) (contKP.stronglyMeasurableAtFilter _ _) contKP.continuousAt
lemma ikM: Monotone ikp:= monotone_of_deriv_nonneg (fun x=>(idk0 x).differentiableAt)
  fun x=>by rw [(idk0 x).deriv]; apply posKP
def zn (n:ℕ):= xs (nd n)
lemma zN0: zn 0=0 := by simp [zn,xs,nd]
lemma zNm:StrictMono zn:= x_mono.comp nd_m
def maxArea (n:ℕ):= (zn (n+1)-zn n)*max 0 (gv (A n).mx)
def arSum : ℕ→ℝ
  | 0=>0
  | n+1=>arSum n+maxArea n
lemma arHI (h:NG) (n:ℕ) (hn:n≤720): ikp (zn n) ≤ arSum n := by
  induction n with
  | zero=>rw [zN0]; simp [arSum,ikp]
  | succ n ih=>
    let a:=gv (A n).mx
    have hz:= (zNm (show n<n+1 by omega)).le
    have he (x) (hx:x∈Icc (zn n) (zn (n+1))) : KP0 x≤ max 0 a := by
      unfold KP0; apply max_le_max le_rfl
      obtain ⟨t,ht⟩:=ontoX x
      rw [← ht] at hx ⊢
      have hh:=((h.good n (by omega)).2 (by omega)).2
      apply hh t ⟨x_mono.le_iff_le.mp hx.1,x_mono.le_iff_le.mp hx.2⟩
    have hK := intervalIntegral.integral_mono_on (μ:=volume) hz (contKP.intervalIntegrable ..)
      (g:=fun _=>max 0 a) intervalIntegrable_const he
    rw [intervalIntegral.integral_const] at hK
    have hIk : ikp (zn n)+(∫ t in (zn n)..(zn (n+1)),KP0 t) = ikp (zn (n+1)) :=
      intervalIntegral.integral_add_adjacent_intervals (contKP.intervalIntegrable ..)
        (contKP.intervalIntegrable ..)
    rw [arSum,← hIk]
    exact add_le_add (ih (by omega)) hK
end
def distB (n:ℕ):IV:= GB (A (n+1)).x-GB (A n).x
def AC : ℕ→IV
  | 0=>0
  | n+1=>AC n+distB n*Zmax 0 (GP (A n).mx)
lemma AC_m (h:NG)(n:ℕ)(hn:n≤720): arSum n∈AC n:= by
  induction n with
  | zero=>exact mz
  | succ n ih=>
    have hz : n ≤720:=by omega
    exact madd (ih hz) (mmul (msub (h.good _ hn).1.xx (h.good _ hz).1.xx)
      (mmax mz (mGP _)))

lemma acs: LeB (AC 720) (bd 3350) && LeB (AC 280) (bd 1260) := by decide +kernel

lemma area0 (h:NG): ikp (zn 720) ≤335/1000 ∧
    ikp (zn 280) ≤ 126/1000:= by
  have hh:=acs; simp only [Bool.and_eq_true] at hh
  have bound (n : ℕ) (hn : n ≤ 720) (a : ℤ) (ha : LeB (AC n) (bd a) = true) :
      ikp (zn n) ≤ (a : ℝ) / 10000 :=
    (arHI h n hn).trans (mle (AC_m h n hn) (mbd a) ha)
  constructor
  · have hi := bound 720 le_rfl 3350 hh.1
    norm_num at hi ⊢
    exact hi
  · have hi := bound 280 (by omega) 1260 hh.2
    norm_num at hi ⊢
    exact hi

noncomputable def wI (x:ℝ):= -(Real.log x+1)/x
noncomputable def wD (x:ℝ):=Real.log x/x^2
lemma Eval_log' {x:ℝ} (hh:0<x): HasDerivAt wI (wD x) x:= by
  convert ((((Real.hasDerivAt_log hh.ne').add_const 1).neg).div (hasDerivAt_id' _) hh.ne') using 1
  all_goals first | rfl | (unfold wD; simp only [Pi.neg_apply]; field_simp; ring)

lemma wBound {x:ℝ} (hx:64 ≤ x): KP0 x ≤ wD x := by
  let y:=Real.log x
  have he: Tail.y0≤y:=Real.log_le_log (by norm_num) hx
  have hh := Tail.kTail he
  have hp : 0<x:= by linarith
  have heq: Tail.XX y = x:= Real.exp_log hp
  obtain ⟨h,h1,-⟩:=hh
  unfold Tail.ev Tail.iv at h1
  rw [heq] at h h1
  have hi:= (mem_band _ _ _).mp h; norm_num at hi
  unfold KP0 wD; rw [max_eq_right hi.1]
  convert h1 using 1; unfold y;ring
lemma w_neg {x:ℝ}(hh:64 ≤ x): wI x ≤ 0 := by
  have he := Real.log_nonneg (show 1≤x by linarith)
  unfold wI; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
lemma wz' (y:ℝ) (he:64 ≤ y): wI 64 ≤ wI y := by
  have hh (y:ℝ) (he:y∈ Ici 64): 0<y:= by change 64 ≤ y at he; linarith
  apply monotoneOn_of_deriv_nonneg (convex_Ici 64)
    (fun y hy=> (Eval_log' (hh _ hy)).continuousAt.continuousWithinAt)
    (fun y hy=> (Eval_log' (hh _ (interior_subset hy))).differentiableAt.differentiableWithinAt) _
    (mem_Ici.mpr (by rfl)) he he
  intro x hx
  have h: 64 ≤ x := interior_subset hx
  rw [(Eval_log' (show 0<x by linarith)).deriv]
  exact le_trans (posKP _) (wBound h)
lemma area_full (h:NG)(x:ℝ): ikp x ≤422/1000 := by
  let z:=zn 720
  have hh :64 ≤ z:= by have ht:=(x720); unfold z zn; linarith
  have hd:ikp z≤335/1000:= (area0 h).1
  rcases le_total x z with he|he
  · apply le_trans (ikM he) (hd.trans (by norm_num))
  have ho (y:ℝ)(hy:y∈uIcc z x):0 < y:= by rw [uIcc_of_le he] at hy;linarith [hy.1]
  have H : ContinuousOn wD (uIcc z x) := by
    unfold wD
    exact ((continuousOn_id.log (fun x hx=>(ho _ hx).ne')).div
      (continuousOn_id.pow _) fun x hx=> pow_ne_zero _ (ho _ hx).ne')
  have hv:=H.intervalIntegrable (μ:=volume)
  have hp:=intervalIntegral.integral_mono_on he (contKP.intervalIntegrable ..) hv
    (fun x hx=>wBound (hh.trans hx.1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx=> Eval_log' (ho _ hx)) hv] at hp
  have hi : ikp z+(∫ t in z..x,KP0 t)=ikp x :=
    intervalIntegral.integral_add_adjacent_intervals (contKP.intervalIntegrable ..)
      (contKP.intervalIntegrable ..)
  have h1 : -(86/1000:ℝ)≤ wI 64 := by
    unfold wI
    have ht:= Tail.ro_lim.2.1; unfold Tail.y0 at ht; linarith
  linarith [w_neg (hh.trans he),wz' z hh]
end GeneralMahler.SCal

end OAI
