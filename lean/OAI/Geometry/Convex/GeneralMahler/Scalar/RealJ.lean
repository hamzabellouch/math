import OAI.Geometry.Convex.GeneralMahler.Intervals.JCalc
import OAI.Geometry.Convex.GeneralMahler.Scalar.Stable

namespace OAI
/-! Finite-real-variable towers in t coordinate. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal
open Profile Layers Jet
def xj : RF := fun x n=> if Even n then xs x else ast x
def aj (x:ℝ):=tail (xj x)
lemma xj0 (x): xj x 0=xs x:=by simp [xj]
lemma aj0 (x): aj x 0=ast x:=by simp [xj,aj,tail]
lemma Ix : TW univ xj := by
  intro n x _
  by_cases h:Even n
  · have he : ¬Even (n+1) := by grind
    simpa only [xj,ite_eq_left h,ite_eq_right he] using xD x
  have he: Even (n+1):= by grind
  simpa only [xj,ite_eq_left he,ite_eq_right h] using aD x
lemma Ia: TW univ aj := Ix.tail

def momRF (i:Nat):RF:= fun x n=> (-1)^n*Ymk (i+n) x
def hfRF:RF:=fun x n=> n.factorial*Qh n x
lemma Imom (i): TW univ (momRF i) := by
  intro n x _
  convert ((DYmk x (i+n)).const_mul ((-1:ℝ)^n)) using 1
  all_goals first|rfl |(unfold momRF; rw [← Nat.add_assoc,pow_succ]; ring)
lemma Ihf: TW (Iio 1) hfRF := by
  intro n x hx
  convert ((hdQ n hx).const_mul ((n.factorial:ℝ))) using 1
  all_goals first|rfl |(unfold hfRF; rw [Nat.factorial_succ]; push_cast; ring)

namespace CJet
def halfS (x:ℝ) := mulJ (ray (1/2)) (mulJ (xj x) (xj x))
def etaS (x:ℝ):= negJ (halfS x)
def ph (x:ℝ):= mulJ (ray (phi 0)) (expSub (etaS x) (Real.exp (etaS x 0)))
def ym (i:Nat) (x:ℝ):= compJ (momRF i (xj x 0)) (xj x)
def Y:RF:= ym 0
def B:RF:=ym 1
def u (x:ℝ):= mulJ (Y x) (ph x)
def p0 (x:ℝ):= subJ (ray 1) (u x)
def h (x:ℝ):= compJ (hfRF (u x 0)) (u x)
def j (x:ℝ):=
  subJ (subJ (plusJ (halfS x) (ray (Real.log (√(2*π)))))
    (logSub vn (Y x) (Real.log (Y x 0)))) (p0 x)
def w (x:ℝ):= subJ (ray 1) (mulJ (p0 x) (B x))
def dj (x:ℝ):= plusJ (mulJ (mulJ (B x) (B x)) (j x)) (mulJ (mulJ (w x) (w x)) (h x))
def gp (x:ℝ):=mulJ (Y x) (subJ (mulJ (B x) (j x)) (mulJ (mulJ (w x) (p0 x)) (h x)))
def kj (x:ℝ):=subJ (plusJ (dj x)
  (mulJ (mulJ (Y x) (Y x)) (plusJ (j x) (mulJ (mulJ (p0 x) (p0 x)) (h x))))) (ray 1)
def cj (x:ℝ):= plusJ (negJ (dj x)) (mulJ (ray (ar-1)) (subJ (mulJ (xj x) (gp x)) (kj x)))
def mc (x:ℝ):=mulJ (ph x) (invSub vn (p0 x))
def jy (x:ℝ):= invSub vn (Y x)
def rv (x:ℝ):= subJ (mc x) (mulJ (B x) (jy x))
def vv (x:ℝ):=
  subJ (subJ (ray (2:ℝ)) (mulJ (mc x) (plusJ (xj x) (mc x)))) (mulJ (mulJ (B x) (jy x)) (jy x))

lemma hs0 (x): halfS x 0= xs x *xs x /2 := by
  change 1/2*(xj x 0*xj x 0)=_; rw [xj0]; ring
lemma ph0 (x): ph x 0=phi (xs x) := by
  change phi 0*Real.exp (-halfS x 0)=_
  rw [hs0]; simp only [phi_apply]; ring_nf; simp
lemma ym0 (i x): ym i x 0=Ymk i (xs x):=by
  change (-1:ℝ)^0*_ =_
  rw [xj0]; ring_nf
lemma Y0 (x): Y x 0=sY (xs x):=ym0 0 _
lemma B0 (x): B x 0=sB (xs x):=ym0 1 _
lemma u0 (x): u x 0=sU (xs x):= by
  change Y x 0*ph x 0=_;rw [Y0,ph0]; rfl
lemma p0v (x): p0 x 0=sP (xs x):=by change 1-u x 0=_; rw [u0]; rfl
lemma h0 (x): h x 0=sH (xs x):= by
  change Nat.factorial 0* Qh 0 (u x 0)=_
  rw [u0]; simp [sH]
lemma j0 (x): j x 0=sJ (xs x):=by
  change halfS x 0+ _-Real.log (Y x 0)-p0 x 0=_
  rw [hs0,Y0,p0v]; rfl
lemma wst (x):w x 0=sW (xs x) := by change 1-p0 x 0 * B x 0=_; rw [p0v,B0]; rfl
lemma d0s (x):dj x 0=sd (xs x):=by
  change B x 0*B x 0*j x 0+w x 0*w x 0*h x 0=_
  rw [B0,j0,wst,h0]; rfl
lemma k0s (x):kj x 0=sK (xs x):=by
  change dj x 0+ Y x 0* Y x 0* (j x 0+p0 x 0*p0 x 0*h x 0)-1=_
  rw [d0s,Y0,j0,p0v,h0]; rfl
lemma c0s (x):cj x 0=sC (xs x):=by
  change -(dj x 0)+(ar-1)*(xj x 0*(Y x 0* (B x 0*j x 0-w x 0*p0 x 0*h x 0))-kj x 0)=_
  rw [xj0,Y0,j0,p0v,h0,B0,wst,d0s,k0s]; rfl
lemma krv (x):rv x 0=sRv (xs x):=by
  change ph x 0*(p0 x 0)⁻¹-B x 0*(Y x 0)⁻¹=_
  rw [ph0,p0v,B0,Y0]; unfold sRv; ring
lemma kvv (x):vv x 0=sV2 (xs x):=by
  change 2-ph x 0*(p0 x 0)⁻¹ * (xj x 0+ph x 0*(p0 x 0)⁻¹)-B x 0*(Y x 0)⁻¹*(Y x 0)⁻¹=_
  rw [ph0,p0v,xj0,B0,Y0]; unfold sV2; dsimp only; ring

lemma Ih : TW univ halfS := (TW.const _).mul (Ix.mul Ix)
lemma Iph : TW univ ph := (TW.const _).mul (Ih.neg.exp)
lemma IY (i): TW univ (ym i) := Ix.comp (Imom i) (fun _ _=>mem_univ _)
lemma Iu: TW univ u:=(IY 0).mul Iph
lemma Ip: TW univ p0:=(TW.const _).sub Iu
lemma ypJ (x): 0 < Y x 0 := Y0 x ▸ Ymp 0 _
lemma ppJ (x): 0 < p0 x 0 := p0v x ▸ (sPe (xs x)).symm ▸ p_pos _
lemma IhJ: TW univ h:= Iu.comp Ihf (fun x _=> by rw [u0]; exact u_le _)
lemma Ij: TW univ j:= ((Ih.add (TW.const _)).sub ((IY 0).log (fun x _=> (ypJ x).ne'))).sub Ip
lemma Iw: TW univ w := (TW.const _).sub (Ip.mul (IY 1))
lemma Id: TW univ dj:= (((IY 1).mul (IY 1)).mul Ij).add ((Iw.mul Iw).mul IhJ)
lemma Ig: TW univ gp:= (IY 0).mul (((IY 1).mul Ij).sub ((Iw.mul Ip).mul IhJ))
lemma IK: TW univ kj:= (Id.add (((IY 0).mul (IY 0)).mul (Ij.add ((Ip.mul Ip).mul IhJ)))).sub (TW.const _)
lemma IC: TW univ cj:= Id.neg.add ((TW.const _).mul ((Ix.mul Ig).sub IK))
lemma Ijy: TW univ jy:= (IY 0).inv (fun x _=> (ypJ x).ne')
lemma Imc: TW univ mc:= Iph.mul (Ip.inv (fun x _=> (ppJ x).ne'))
lemma Irv: TW univ rv:= Imc.sub ((IY 1).mul Ijy)
lemma Ivv: TW univ vv:= ((TW.const _).sub (Imc.mul (Ix.add Imc))).sub (((IY 1).mul Ijy).mul Ijy)
end CJet
end GeneralMahler.SCal

end

end OAI
