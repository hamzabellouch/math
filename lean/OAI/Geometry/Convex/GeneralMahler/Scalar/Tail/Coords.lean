import OAI.Geometry.Convex.GeneralMahler.Scalar.Tail.Enclose

namespace OAI
/-! Convert tail jets into coordinate and number operator bounds. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail
open JT JTB Grid Jet Tag Cert Cert.IV Profile Layers
noncomputable section
def rrF (x:ℝ):= subJ (ray CJet.radK) (dF x)
def ql (x:ℝ):=
  let A:=rrF x
  subJ (ray kk) (rootSub (1/2) vn A (Real.sqrt (A 0)))
lemma rre0 (x:ℝ):rrF x 0=rad (XX x):=by change CJet.radK - dF x 0=_;rw [dF0,rad,pow_two];rfl
lemma qe0 (x:ℝ):ql x 0=qu (XX x):= by change kk-√(rrF x 0)=_;rw [rre0];rfl
lemma Twq (h:CJet.RadH):TW univ ql := (TW.const _).sub
  (((TW.const _).sub TdF).root (fun x _ =>by change 0< rrF x 0; rw [rre0]; exact h _))

def bt (t y:ℝ):= ast t*iv y
lemma dots_log {x y:ℝ} (hh:xs x=XX y) {F:RF} (h:TW univ F) {f:ℝ→ℝ} (hf:TestF f)
    (he:∀ t,F t 0=f (XX t)) :
    let G:=bt x y
    DotF f x=G*F y 1 ∧ NNf f x = G^2*(F y 2-F y 1) ∧
      DDot f x=G^2*(F y 2-F y 1)+F y 1 ∧
      N2 f (xs x)=2*F y 0+F y 1-ev y*(F y 2-F y 1) := by
  intro G
  obtain ⟨hp,hv⟩:=path y f hf F h he
  have h₁:= (d_lift hf x).deriv
  have ha:=SCov f hf x
  have h₂:= (dd_lift hf x).deriv
  rw [hh] at h₁ h₂ ha
  have hQ:=xP y
  refine ⟨?_,?_,?_,?_⟩
  · unfold DotF; rw [h₁,hp]; unfold G bt iv; field_simp
  · rw [ha.1,hv]; unfold G bt iv; field_simp; ring
  · unfold DDot
    rw [h₂,hv,hp]; unfold G bt iv; field_simp; ring
  rw [hh,N2,N,hv,hp,he]; unfold ev iv; field_simp; ring
lemma bt_bound {x y:ℝ} (hh:xs x=XX y) (h:y0 ≤ y): 0 ≤ bt x y ∧ bt x y ≤1002/1000 := by
  have hp:=xP y
  have ha := ap x
  have hu:= (vsmall h).1
  unfold bt iv
  have he : ast x ^2 = xs x ^2+ sb^2 := by
    unfold ast xs
    have hi:= Real.cosh_sq_sub_sinh_sq x
    linear_combination sb^2*hi
  refine ⟨mul_nonneg ha.le (by positivity),?_⟩
  rw [← div_eq_mul_inv,div_le_iff₀ hp]
  rw [hh] at he; unfold sb at *
  nlinarith
end

def bRat:=IV.span 0 (IV.c 1002/IV.c 1000)
def bRj:=subJ (ray Row0.radB) bdF
def bQj:=subJ (ray Row0.kkB)
  (rootSub (1/2) ub bRj (rtB (bRj 0)))
def ba (f:J IV):= bRat*f 1
def bbN (f:J IV):= sq bRat*(f 2-f 1)
def bdN (f:J IV):= bbN f+f 1
def bS2 (f:J IV):=2*f 0+f 1-XI*(f 2-f 1)

lemma mRj {x:ℝ} (hv:y0 ≤ x): Fits (rrF x) bRj:=
  (Fits.ray Row0.mradB).sub (fdF hv)
private lemma mqReduce {X:J ℝ} {A:J IV} (h:Fits X A):
    Fits (subJ (ray kk) (rootSub (1/2) vn X (√(X 0))))
      (subJ (ray Row0.kkB) (rootSub (1/2) ub A (rtB (A 0)))) :=
  (Fits.ray Row0.mkkB).sub (h.rt (mrt (h 0)))
lemma mQl {x:ℝ} (hv:y0 ≤ x): Fits (ql x) bQj:= mqReduce (mRj hv)
lemma mDots {x y:ℝ} (hh:xs x=XX y) (he:y0 ≤ y) {F:RF}{A:J IV} (h:TW univ F)
    {f:ℝ→ℝ} (hf:TestF f) (hv:∀ t,F t 0=f (XX t)) (hj:Fits (F y) A):
    DotF f x∈ba A ∧ NNf f x∈bbN A∧ DDot f x∈ bdN A∧
      N2 f (xs x)∈bS2 A := by
  have hi:=bt_bound hh he
  have hu:bt x y ∈bRat := by
    apply span_conv mz (mdiv (mc 1002) (mc 1000)) hi.1
    exact hi.2
  obtain ⟨h₁,h₂,h₃,h₄⟩:=dots_log hh h hf hv
  rw [h₁,h₂,h₃,h₄]
  have hp:= msub (hj 2) (hj 1)
  have hq:= mmul (msq hu) hp
  exact ⟨mmul hu (hj 1),hq,madd hq (hj 1),
    msub (madd (mmul mtwo (hj 0)) (hj 1)) (mmul (lXI he) hp)⟩
end GeneralMahler.SCal.Tail

end OAI
