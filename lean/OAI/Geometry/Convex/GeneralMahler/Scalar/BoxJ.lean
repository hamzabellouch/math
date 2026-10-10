import OAI.Geometry.Convex.GeneralMahler.Scalar.RealJ
import OAI.Geometry.Convex.GeneralMahler.Scalar.LapBox
import OAI.Geometry.Convex.GeneralMahler.Scalar.HBox

namespace OAI
/-! Interval enclosures for profile derivative towers from hyperbolic coordinates
and bounds for the Laplace moments `Ymk`. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Profile Layers Jet Cert Cert.IV
structure Row0 where
  X:IV
  T:IV
  mm:ℕ→IV

namespace Row0
def sbB: IV:= IV.c 36/IV.c 10
def arB: IV:=IV.c 75/IV.c 10
def bSinh (U:IV):IV:= (ebox 5 U-(ebox 5 U)⁻¹)/ (2:IV)
def bCosh (U:IV):IV:= (ebox 5 U+(ebox 5 U)⁻¹)/ (2:IV)
lemma msbB : sb∈sbB := by
  have hh:=mdiv (mc 36) (mc 10)
  norm_num [sb] at *; exact hh
lemma marB : ar∈arB := by
  have hh:=mdiv (mc 75) (mc 10)
  norm_num [ar] at *; exact hh
lemma mHyp {U:IV} {x:ℝ} (hx:x∈U): Real.sinh x∈bSinh U ∧ Real.cosh x∈bCosh U := by
  rw [Real.sinh_eq,Real.cosh_eq, Real.exp_neg]
  have he:= mebox 5 hx
  exact ⟨mdiv (msub he (minv he)) mtwo,mdiv (madd he (minv he)) mtwo⟩
def point (x:IV):Row0 :=
  let T:=sbB*bSinh x
  ⟨T,sbB*bCosh x,fun i=>ymBox i T⟩

def around (x y:Row0): Row0:=
  ⟨IV.span x.X y.X,IV.span x.T y.T,fun i=>IV.span (y.mm i) (x.mm i)⟩

structure At (x:ℝ) (w:Row0): Prop where
  X: xs x∈ w.X
  T: ast x∈ w.T
  mm:∀ n,Ymk n (xs x)∈ w.mm n
lemma at_point {x:ℝ} {B:IV} (hx:x∈B): At x (point B) := by
  have hi:=mHyp hx
  have hs : xs x∈sbB*bSinh B := mmul msbB hi.1
  exact ⟨hs,mmul msbB hi.2,fun i=>myBox hs i⟩
lemma at_segment {x y z:ℝ} {A B:Row0} (ha:At x A) (hb:At y B)
    (he:0≤x) (h:x≤z) (hh:z≤y): At z (around A B) := by
  have hz:= x_mono.monotone h
  have ht:= x_mono.monotone hh
  have hc : MonotoneOn ast (Ici 0) := by
    intro x hx y hy h
    unfold ast
    apply mul_le_mul_of_nonneg_left _ hsb.le
    apply Real.cosh_le_cosh.mpr; rw [abs_of_nonneg hx,abs_of_nonneg hy]; exact h
  have hv:=he.trans h
  have hp:=hv.trans hh
  exact ⟨span_conv ha.X hb.X hz ht,
    span_conv ha.T hb.T (hc he hv h) (hc hv hp hh),
    fun i=>span_conv (hb.mm i) (ha.mm i) ((Yanti i).antitone ht) ((Yanti i).antitone hz)⟩
variable (w:Row0)
def Xj : J IV:=fun n=> if n%2=0 then w.X else w.T
def Ym (i:Nat) := compJ (fun n=> (-(1:IV))^n*w.mm (i+n)) w.Xj
def Y:= w.Ym 0
def B := w.Ym 1
def hsS:= mulJ (ray (1/2:IV)) (mulJ w.Xj w.Xj)
def Ph :=
  let f:=negJ w.hsS
  mulJ (ray phi0B) (expSub f (ebox 14 (f 0)))
def U := mulJ w.Y w.Ph
def P0:= subJ (ray 1) w.U
def W0:= subJ (ray 1) (mulJ w.P0 w.B)
def Hj:=
  let R:=w.U 0
  compJ (fun n=> IV.c (Int.ofNat n.factorial)*hBox R n (if LeB R (IV.c 8/IV.c 100) then 18 else 42)) w.U
def J0:=
  let A:=rtB ((2:IV)*piB)
  subJ (subJ (plusJ w.hsS (ray (lbox 6 A)))
    (logSub ub w.Y (lbox 6 (w.Y 0)))) w.P0
def Dj:= plusJ (mulJ (mulJ w.B w.B) w.J0) (mulJ (mulJ w.W0 w.W0) w.Hj)
def Kj:= subJ (plusJ w.Dj (mulJ (mulJ w.Y w.Y)
  (plusJ w.J0 (mulJ (mulJ w.P0 w.P0) w.Hj)))) (ray 1)
def Gp:= mulJ w.Y (subJ (mulJ w.B w.J0) (mulJ (mulJ w.W0 w.P0) w.Hj))
def Cj:=plusJ (negJ w.Dj) (mulJ (ray (arB-1)) (subJ (mulJ w.Xj w.Gp) w.Kj))
def Mc:=mulJ w.Ph (invSub ub w.P0)
def JY:=invSub ub w.Y
def Rv:=subJ w.Mc (mulJ w.B w.JY)
def Vv:=subJ (subJ (ray (2:IV)) (mulJ w.Mc (plusJ w.Xj w.Mc))) (mulJ (mulJ w.B w.JY) w.JY)

namespace At
open CJet
variable {w:Row0} {x:ℝ} (h:At x w)
include h
lemma mXj : Fits (xj x) w.Xj := by
  unfold xj Xj
  intro n
  by_cases he:n%2=0
  · simpa only [Nat.even_iff,ite_eq_left he] using h.X
  simpa only [Nat.even_iff,ite_eq_right he] using h.T
lemma ms : Fits (halfS x) w.hsS :=
  (Fits.ray mhalf).mul (h.mXj.mul h.mXj)
lemma mP : Fits (ph x) w.Ph := by
  have hi := h.ms.neg
  exact (Fits.ray mphi0).mul (hi.exp (mebox 14 (hi 0)))
lemma mY (i:ℕ): Fits (ym i x) (w.Ym i) := by
  apply h.mXj.comp
  intro n
  unfold momRF; rw [xj0]
  exact mmul (mpow (mneg mo) _) (h.mm _)
lemma mU : Fits (u x) w.U := (h.mY 0).mul h.mP
lemma mP0: Fits (p0 x) w.P0:=(Fits.ray mo).sub h.mU
lemma mW: Fits (CJet.w x) w.W0 := (Fits.ray mo).sub (h.mP0.mul (h.mY 1))
lemma mH: Fits (CJet.h x) w.Hj := by
  unfold CJet.h Hj; dsimp only
  apply h.mU.comp
  intro n
  have he : 0<sU (xs x) := u_pos _
  have hp := u_le (xs x)
  have hh:=u0 x
  rw [← hh] at he hp
  exact mmul (nc _) (mhBox _ _ he.le hp (h.mU 0))
lemma mJ: Fits (CJet.j x) w.J0 :=
  ((h.ms.add (Fits.ray (mlbox (mrt (mmul mtwo mpi)) _))).sub
    ((h.mY 0).log (mlbox (h.mY 0 0) _))).sub h.mP0
lemma mD: Fits (CJet.dj x) w.Dj :=
  ((((h.mY 1).mul (h.mY 1)).mul h.mJ).add ((h.mW.mul h.mW).mul h.mH))
lemma mK: Fits (CJet.kj x) w.Kj := (h.mD.add (((h.mY 0).mul (h.mY 0)).mul
    (h.mJ.add ((h.mP0.mul h.mP0).mul h.mH)))).sub (Fits.ray mo)
lemma mC: Fits (CJet.cj x) w.Cj := by
  have ih : Fits (CJet.gp x) w.Gp := (h.mY 0).mul (((h.mY 1).mul h.mJ).sub ((h.mW.mul h.mP0).mul h.mH))
  exact h.mD.neg.add ((Fits.ray (msub marB mo)).mul ((h.mXj.mul ih).sub h.mK))
lemma mMc: Fits (CJet.mc x) w.Mc:=h.mP.mul h.mP0.inv
lemma mJy: Fits (CJet.jy x) w.JY:=(h.mY 0).inv
lemma mRv: Fits (CJet.rv x) w.Rv:=h.mMc.sub ((h.mY 1).mul h.mJy)
lemma mVv: Fits (CJet.vv x) w.Vv:=
  ((Fits.ray mtwo).sub (h.mMc.mul (h.mXj.add h.mMc))).sub (((h.mY 1).mul h.mJy).mul h.mJy)
end At
end Row0
end GeneralMahler.SCal

end OAI
