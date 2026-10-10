import OAI.Geometry.Convex.GeneralMahler.Scalar.Tail.Limit
import OAI.Geometry.Convex.GeneralMahler.Scalar.Tail.Tower

namespace OAI
/-! Interval AD bounding envelopes DD, CQ, KR. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail.JTB
open JT Grid Profile Tag Cert Cert.IV Jet Layers
def bmJ : J IV:= fun n=> mr n 0 0
def bnJ : J IV:= fun n=> mr n 1 0
def bt1: J IV:= fun n=> pr n 1
def bPt:=mulJ bt1 bmJ
def bU := mulJ BI bPt
def bPP:= subJ (ray 1) bU
def bPQ:= mulJ bPP bPP
def hf0:J IV:= fun n=> ub n.factorial * hBox (bU 0) n 7
def bHH:=compJ hf0 bU
def bH1:=compJ (tail hf0) bU
def bDH:=mulJ (mulJ (ray (1/2)) bPt) (subJ (invSub ub bPP) bH1)
def bM:=mulJ bmJ bmJ
def bN:=mulJ bnJ bnJ
def bDel:=plusJ (subJ (negJ (logSub ub bmJ (lbox 5 (bmJ 0)))) (subJ bPP (ray 1)))
  (subJ (mulJ bPQ bHH) (ray (1/2)))
def bZ:=plusJ wr (mulJ BI bDel)
def bA:=subJ (mulJ (ray (1/2)) bN)
  (mulJ (mulJ (mulJ (ray 2) bPP) bHH) bnJ)
def bMi:=mulJ bnJ (plusJ (ray 1) bmJ)
def bN1:=mulJ BI bN
def bDD:= plusJ (plusJ bDH bA) (mulJ bN bZ)
def bG:=subJ (mulJ (mulJ (ray (1/4)) BI) bMi)
  (mulJ (mulJ (ray (1/2)) bM) bZ)
def bKR:=
  plusJ (plusJ (plusJ (plusJ (subJ (plusJ bDH bA) bnJ)
    (mulJ (ray (1/2)) bN1)) (ray (3/2)))
    (mulJ (plusJ bM bN1) bDel))
    (mulJ (subJ bN bMi) wr)
def bCQ:=
  subJ (mulJ (ray (Row0.arB-1)) (subJ (tail (tail bG)) (tail bG))) bDD
def bdF:=plusJ (ray (1/2)) (mulJ BI bDD)
def bkF:=plusJ wr (mulJ BI (subJ bKR (ray (3/2))))
def bcF:=subJ (mulJ BI bCQ) (ray (1/2))

lemma mquarter : (1/4:ℝ)∈(1/4:IV) :=
  mdiv mo (mc 4)
lemma m32: (3/2:ℝ)∈(3/2:IV):=
  mdiv (mc 3) mtwo

variable {x:ℝ} (h:y0≤x)
include h
lemma fmJ: Fits (MJ x) bmJ:=lTm h 0 0
lemma fnJ:Fits (NJ x) bnJ:= lTm h 1 0
lemma fPt: Fits (JT.Pt x) bPt:= (lpF h 1).mul (fmJ h)
lemma fU: Fits (U x) bU:= (lBI h).mul (fPt h)
lemma fPP: Fits (PP x) bPP:= (Fits.ray mo).sub (fU h)
lemma fhf0: Fits (hfRF (U x 0)) hf0:= by
  have hi:= fU h 0
  have he: 0<U x 0:=by rw [U0]; apply u_pos
  have hh: U x 0<1:= huJ x
  intro n; exact mmul (nc _) (mhBox n _ he.le hh hi)
lemma fbH: Fits (JT.HH x) bHH:= (fU h).comp (fhf0 h)
lemma fbH1: Fits (JT.H1 x) bH1:= (fU h).comp (fhf0 h).drop
lemma fbDH: Fits (DH x) bDH :=
  ((Fits.ray mhalf).mul (fPt h)).mul ((fPP h).inv.sub (fbH1 h))
lemma fbM: Fits (M2 x) bM:= (fmJ h).mul (fmJ h)
lemma fbN: Fits (NN x) bN:= (fnJ h).mul (fnJ h)
lemma fbD: Fits (del x) bDel:=
  ((((fmJ h).log (mlbox (fmJ h 0) _)).neg.sub ((fPP h).sub (Fits.ray mo))).add
    ((((fPP h).mul (fPP h)).mul (fbH h)).sub (Fits.ray mhalf)))
lemma fbZ: Fits (wZ x) bZ := (lwr h).add ((lBI h).mul (fbD h))
lemma fbA: Fits (JT.A x) bA:= ((Fits.ray mhalf).mul (fbN h)).sub
  ((((Fits.ray mtwo).mul (fPP h)).mul (fbH h)).mul (fnJ h))
lemma fbMi: Fits (mi x) bMi:=(fnJ h).mul ((Fits.ray mo).add (fmJ h))
lemma fDD: Fits (DD x) bDD:=((fbDH h).add (fbA h)).add ((fbN h).mul (fbZ h))
lemma fbG: Fits (G0 x) bG:=
  (((Fits.ray mquarter).mul (lBI h)).mul (fbMi h)).sub (((Fits.ray mhalf).mul (fbM h)).mul (fbZ h))
lemma fbN1: Fits (N1 x) bN1:=(lBI h).mul (fbN h)
lemma fKR: Fits (KR x) bKR:=
  (((((((fbDH h).add (fbA h)).sub (fnJ h)).add ((Fits.ray mhalf).mul (fbN1 h))).add
    (Fits.ray m32)).add (((fbM h).add (fbN1 h)).mul (fbD h))).add
    (((fbN h).sub (fbMi h)).mul (lwr h)))
lemma fCQ: Fits (CQ x) bCQ:=
  ((Fits.ray (msub Row0.marB mo)).mul ((fbG h).drop.drop.sub (fbG h).drop)).sub (fDD h)
lemma fdF: Fits (dF x) bdF:= (Fits.ray mhalf).add ((lBI h).mul (fDD h))
lemma fcF: Fits (cF x) bcF:= ((lBI h).mul (fCQ h)).sub (Fits.ray mhalf)
lemma fkF: Fits (kF x) bkF:=
  (lwr h).add ((lBI h).mul ((fKR h).sub (Fits.ray m32)))
end GeneralMahler.SCal.Tail.JTB

end OAI
