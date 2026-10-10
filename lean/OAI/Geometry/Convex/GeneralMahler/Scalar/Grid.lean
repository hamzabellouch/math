import OAI.Geometry.Convex.GeneralMahler.Intervals.Chord
import OAI.Geometry.Convex.GeneralMahler.Scalar.QuantJ
import OAI.Geometry.Convex.GeneralMahler.Linear.Powers

namespace OAI
/-! Finite interval cells of appendix §07. Actual tagged values. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Profile Jet CJet
inductive Tag
  | R | K | C | Q | dK | dC | dQ | ddK | ddC | ddQ | NK | NC | NQ | RV | V | S
deriving DecidableEq, Repr
namespace Tag

instance : Fintype Tag :=
  Fintype.ofList [R, K, C, Q, dK, dC, dQ, ddK, ddC, ddQ, NK, NC, NQ, RV, V, S]
    (by intro t; cases t <;> simp)

noncomputable def Fld : Tag→RF
  | R=>rj
  | K=>kj
  | C=>cj
  | Q=>qj
  | dK=> fun x=> tail (kj x)
  | dC=> fun x=> tail (cj x)
  | dQ=> fun x=> tail (qj x)
  | ddK=> fun x=>tail (tail (kj x))
  | ddC=> fun x=>tail (tail (cj x))
  | ddQ=> fun x=>tail (tail (qj x))
  | NK=> NJ kj
  | NC=> NJ cj
  | NQ=> NJ qj
  | RV=>rv
  | V=>vv
  | S=>Sf qj

noncomputable def act : Tag→ℝ→ℝ
  | R=> liftF rad
  | K=> liftF Kp
  | C=> liftF Cp
  | Q=> liftF qu
  | dK=> DotF Kp
  | dC=> DotF Cp
  | dQ=> DotF qu
  | ddK=> DDot Kp
  | ddC=> DDot Cp
  | ddQ=> DDot qu
  | NK=> NNf Kp
  | NC=> NNf Cp
  | NQ=> NNf qu
  | RV=> liftF fun x=> deriv v x-x
  | V=> liftF (deriv (deriv v))
  | S=> liftF (N2 qu)

open Cert Cert.IV
def Jt (t:Tag) (w:Row0): J IV := match t with
  | R=>w.Rj
  | K=>w.Kj
  | C=>w.Cj
  | Q=>w.Qj
  | dK=>tail w.Kj
  | dC=>tail w.Cj
  | dQ=>tail w.Qj
  | ddK=>tail (tail w.Kj)
  | ddC=>tail (tail w.Cj)
  | ddQ=>tail (tail w.Qj)
  | NK=>w.NB w.Kj
  | NC=>w.NB w.Cj
  | NQ=>w.NB w.Qj
  | RV=>w.Rv
  | V=>w.Vv
  | S=>w.SF w.Qj

lemma tower (i:Tag) (h:CJet.RadH) : TW univ (Fld i) := by
  have ha:=IK; have hb:=IC; have he:=IQ h
  cases i
  · exact Ir
  · exact ha
  · exact hb
  · exact he
  · exact ha.tail
  · exact hb.tail
  · exact he.tail
  · exact ha.tail.tail
  · exact hb.tail.tail
  · exact he.tail.tail
  · exact IN kj ha
  · exact IN cj hb
  · exact IN qj he
  · exact Irv
  · exact Ivv
  · exact IS qj he
lemma FldK (x): Fld K x 0=Kp (xs x):= (k0s x).trans (k_stable _)
lemma FldC (x): Fld C x 0=Cp (xs x):= (c0s x).trans (c_stable _)
lemma field_val (h:CJet.RadH) (hQ:TestF qu) (i:Tag) (x:ℝ) :
    Fld i x 0=act i x := by
  have heq : (fun x=>qj x 0)=liftF qu:= funext qje
  obtain ⟨ha,hb,hc⟩:= nj0 kj Kp IK (funext FldK) x
  obtain ⟨hh,hi,hj⟩:= nj0 cj Cp IC (funext FldC) x
  obtain ⟨hf,hg,hq⟩:= nj0 qj qu (IQ h) heq x
  cases i
  · exact rje x
  · exact FldK x
  · exact FldC x
  · exact qje x
  · exact ha
  · exact hh
  · exact hf
  · exact hb
  · exact hi
  · exact hg
  · exact hc
  · exact hj
  · exact hq
  · exact (krv x).trans (rv_stable _)
  · exact (kvv x).trans (v2_stable _)
  · exact sj0 qj qu (IQ h) heq hQ x
lemma fit {w:Row0} {x:ℝ} (h:Row0.At x w) (i:Tag) : Fits (Fld i x) (Jt i w) := by
  have ha := h.mK; have hb:= h.mC; have hc:= h.mQJ
  cases i
  · exact h.mRJ
  · exact ha
  · exact hb
  · exact hc
  · exact ha.drop
  · exact hb.drop
  · exact hc.drop
  · exact ha.drop.drop
  · exact hb.drop.drop
  · exact hc.drop.drop
  · exact h.mNJ (X:=kj) ha
  · exact h.mNJ (X:=cj) hb
  · exact h.mNJ (X:=qj) hc
  · exact h.mRv
  · exact h.mVv
  · exact h.mSf (X:=qj) hc
end Tag

namespace Grid
open Tag Cert Cert.IV
-- finite mesh: t_j=j/200
noncomputable def nd (n:ℕ):ℝ:= n/200
def deltG:IV:= (1:IV)/(IV.c 200)
def nbox (n:ℕ):IV:= IV.c (Int.ofNat n)/IV.c 200
lemma mgrid (n:ℕ):nd n∈nbox n := mdiv (nc n) (mc 200)
lemma n_nn (n:ℕ):0≤nd n := by unfold nd; positivity
lemma dcell (n:ℕ): nd (n+1)-nd n∈deltG := by
  rw [show nd (n+1)-nd n=1/200 from by unfold nd; push_cast; ring]
  exact mdiv mo (mc 200)

def pG (n:ℕ): Row0:=Row0.point (nbox n)
def pc (n:ℕ):Row0:=Row0.around (pG n) (pG (n+1))
lemma pGa (n:ℕ):Row0.At (nd n) (pG n) := Row0.at_point (mgrid n)
lemma pca (n:ℕ) (x) (hx:x∈Icc (nd n) (nd (n+1))):
    Row0.At x (pc n) := Row0.at_segment (pGa _) (pGa _) (n_nn _) hx.1 hx.2

def cb0 (n:ℕ) (t:Tag) (i:ℕ) (F:IV):IV:= bcChord deltG
  (t.Jt (pG n) i) (t.Jt (pG (n+1)) i) F
def cb (n:ℕ) (t:Tag) (i:ℕ):IV:= cb0 n t i (t.Jt (pc n) (i+2))
def sharp : Tag→Bool
  | R|K|C|Q=>true
  | _=>false
def tot (n:ℕ) (t:Tag):IV:= if sharp t then cb0 n t 0 (cb n t 2) else cb n t 0
lemma hcb0 (n:ℕ) (t:Tag) (i:ℕ) (F:IV) (ht:TW univ (Fld t))
    (he:∀ x∈Icc (nd n) (nd (n+1)),t.Fld x (i+2)∈F)
    (x:ℝ) (hx:x∈Icc (nd n) (nd (n+1))) :
    t.Fld x i ∈ cb0 n t i F :=
  mcChord _ ht i (nd n) (nd (n+1)) x hx.1 hx.2 _ _ _ _
    (fit (pGa _) t _) (fit (pGa _) t _) (dcell n) he

lemma hcb (n:ℕ) (t:Tag) (i:ℕ) (ht:TW univ (Fld t))
    (x:ℝ) (hx:x∈Icc (nd n) (nd (n+1))) :
    t.Fld x i ∈ cb n t i :=
  hcb0 n t i _ ht (fun x hx=>fit (pca n x hx) t _) x hx

lemma htot (n:ℕ) (t:Tag) (ht:TW univ (Fld t))
    (x:ℝ) (hx:x∈Icc (nd n) (nd (n+1))) :
    t.Fld x 0∈tot n t := by
  unfold tot; split
  · exact hcb0 n t _ _ ht (hcb n t 2 ht) x hx
  exact hcb n t _ ht x hx
end Grid
end GeneralMahler.SCal

end OAI
