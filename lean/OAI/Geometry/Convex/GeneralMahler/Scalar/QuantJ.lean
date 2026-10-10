import OAI.Geometry.Convex.GeneralMahler.Scalar.BoxJ

namespace OAI
/-! Towers for q, N profiles and field composition identities. -/
open Set Filter MeasureTheory MeasureTheory.Measure Real
namespace GeneralMahler.SCal
open Profile Layers Jet
noncomputable section
def DotF (f:ℝ→ℝ):=deriv (liftF f)
def DDot (f:ℝ→ℝ):=deriv (DotF f)
def thR (x:ℝ):=xs x/ ast x
def NNf (f:ℝ→ℝ) (x:ℝ):= DDot f x-thR x * DotF f x
lemma th_eq (x): thR x=Real.tanh x := by
  unfold thR xs ast; rw [Real.tanh_eq_sinh_div_cosh]; field_simp [hsb.ne']
lemma d_lift {f:ℝ→ℝ} (hf:TestF f) (x:ℝ):
    HasDerivAt (liftF f) (ast x*deriv f (xs x)) x := by
  rw [mul_comm]; exact (hf.diff _).hasDerivAt.comp x (xD x)
lemma dd_lift {f:ℝ→ℝ} (hf:TestF f) (x):
    HasDerivAt (DotF f)
      (xs x * deriv f (xs x) + ast x * (ast x*deriv (deriv f) (xs x))) x := by
  have hh : DotF f=fun x=> ast x*deriv f (xs x):=funext fun x=> (d_lift hf x).deriv
  rw [hh]
  exact (aD x).mul (d_lift hf.der x)
lemma SCov (f:ℝ→ℝ) (hf:TestF f) (x):
    NNf f x = ast x^2*deriv (deriv f) (xs x) ∧
    N2 f (xs x) = 2*f (xs x)+ thR x*DotF f x-
      (ast x)⁻¹ *((ast x)⁻¹)* NNf f x := by
  have hh : DotF f x=_:= (d_lift hf x).deriv
  unfold NNf; rw [DDot,(dd_lift hf x).deriv,hh]; unfold N2 N thR
  have hp := (ap x)
  constructor <;> field_simp <;> ring

namespace CJet
def radK:=bb-r*r
def rj (x:ℝ):=subJ (ray radK) (dj x)
def el (x:ℝ):=rootSub (1/2) vn (rj x) (Real.sqrt (rj x 0))
def qj (x:ℝ):=subJ (ray kk) (el x)
def it (x:ℝ):=invSub vn (aj x)
def tj (x:ℝ):=mulJ (xj x) (it x)
def NJ (X:RF) (x:ℝ):=
  subJ (tail (tail (X x))) (mulJ (tj x) (tail (X x)))
def Sf (X:RF) (x:ℝ):=
  subJ (plusJ (mulJ (ray 2) (X x)) (mulJ (tj x) (tail (X x))))
    (mulJ (mulJ (it x) (it x)) (NJ X x))

def RadH := ∀ x, 0<rad x
lemma rje (x): rj x 0=rad (xs x) := by change radK - dj x 0=_; rw [d0s,d_stable,rad,pow_two];rfl
lemma qje (x): qj x 0 = qu (xs x) := by change kk-√(rj x 0)=_; rw [rje]; rfl
lemma Ir: TW univ rj:= (TW.const _).sub Id
lemma Ie (h:RadH): TW univ el := Ir.root (fun x _=> by rw [rje]; exact h _)
lemma IQ (h:RadH): TW univ qj:= (TW.const _).sub (Ie h)
lemma It: TW univ it := Ia.inv (fun x _=> by rw [aj0]; exact (ap x).ne')
lemma IT: TW univ tj:=Ix.mul It
lemma IN (X:RF) (h:TW univ X): TW univ (NJ X):= h.tail.tail.sub (IT.mul h.tail)
lemma IS (X:RF) (h:TW univ X): TW univ (Sf X):=
  (((TW.const _).mul h).add (IT.mul h.tail)).sub ((It.mul It).mul (IN X h))

lemma nj0 (X:RF) (f:ℝ→ℝ) (h:TW univ X) (he:(fun x=>X x 0)=liftF f) (x:ℝ):
    X x 1=DotF f x ∧ X x 2=DDot f x ∧ NJ X x 0= NNf f x := by
  have hh (i:Nat): X x i=dV (liftF f) i x := by rw [← he]; exact (V_eq h isOpen_univ i (mem_univ x)).symm
  have hx : X x 1=DotF f x := hh 1
  have hy : X x 2= DDot f x:= hh 2
  refine ⟨hx,hy,?_⟩
  change X x 2-xj x 0*(aj x 0)⁻¹*X x 1= _
  rw [hx,hy,xj0,aj0]
  unfold NNf thR; ring
lemma sj0 (X:RF) (f:ℝ→ℝ) (h:TW univ X) (he:(fun x=>X x 0)=liftF f) (hf:TestF f) (x):
    Sf X x 0= N2 f (xs x) := by
  obtain ⟨ha,hb,hc⟩:= nj0 X f h he x
  change 2*X x 0+xj x 0*(aj x 0)⁻¹*X x 1-((aj x 0)⁻¹*(aj x 0)⁻¹)*NJ X x 0=_
  have he' : X x 0=f (xs x):= congrFun he x
  rw [he',ha,xj0,aj0,hc,(SCov f hf x).2]
  unfold thR; ring
end CJet
end

open Cert Cert.IV
namespace Row0
variable (w:Row0)
def bbB:IV:=IV.c 602/IV.c 1000
def ccB:IV:=IV.c 365/IV.c 1000
def rB:IV:=IV.c 22/IV.c 100
def kkB:IV:= rtB (bbB-ccB)
def radB:=bbB-rB*rB
def Rj:=subJ (ray radB) w.Dj
def elB:=rootSub (1/2) ub w.Rj (rtB (w.Rj 0))
def Qj:=subJ (ray kkB) w.elB
def itB:=invSub ub (tail w.Xj)
def tjB:=mulJ w.Xj w.itB
def NB (X:J IV):=subJ (tail (tail X)) (mulJ w.tjB (tail X))
def SF (X:J IV):=
  subJ (plusJ (mulJ (ray 2) X) (mulJ w.tjB (tail X)))
    (mulJ (mulJ w.itB w.itB) (w.NB X))

lemma mbb: bb∈bbB := by have hh:=mdiv (mc 602) (mc 1000);norm_num [bb] at *; exact hh
lemma mcc: cc∈ccB := by have hh:=mdiv (mc 365) (mc 1000);norm_num [cc] at *; exact hh
lemma mrB : Profile.r∈rB := by have hh:=mdiv (mc 22) (mc 100);norm_num [Profile.r] at *; exact hh
lemma mradB: CJet.radK∈ radB := msub mbb (mmul mrB mrB)
lemma mkkB:kk∈ kkB := mrt (msub mbb mcc)
namespace At
open CJet
variable {w:Row0}{x:ℝ}(h:At x w)
include h
lemma mRJ: Fits (rj x) w.Rj := (Fits.ray mradB).sub h.mD
lemma mQJ: Fits (qj x) w.Qj := (Fits.ray mkkB).sub (h.mRJ.rt (mrt (h.mRJ 0)))
lemma mit: Fits (it x) w.itB := h.mXj.drop.inv
lemma mtj: Fits (tj x) w.tjB := h.mXj.mul h.mit
lemma mNJ {X:RF} {A:J IV} (he:Fits (X x) A): Fits (NJ X x) (w.NB A) :=
  he.drop.drop.sub (h.mtj.mul he.drop)
lemma mSf {X:RF} {A:J IV} (he:Fits (X x) A): Fits (Sf X x) (w.SF A):=
  (((Fits.ray mtwo).mul he).add (h.mtj.mul he.drop)).sub ((h.mit.mul h.mit).mul (h.mNJ he))
end At
end Row0
end GeneralMahler.SCal

end OAI
