import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeErasure
import OAI.Combinatorics.MatchingCount.Sampling.TreeIndexedPairCorrect

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeFraction TreeTyped.SparseProgram TreeTyped.Numbered

variable {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
def typedP (x : Context×(E×V)) : Bool := p (x.1,(index x.2.1,index x.2.2))
def typedQ (x : Context×(E×E)) : Bool := q (x.1,(index x.2.1,index x.2.2))
def typedR (x : Context×(E×(V×V))) : Bool := r (x.1,(index x.2.1,(index x.2.2.1,index x.2.2.2)))
def typedT (x : Context×(E×E)) : Bool := t (x.1,(index x.2.1,index x.2.2))
def typedU (x : Context×E) : Fraction := u (x.1,index x.2)
def typedV (x : Context×E) : Fraction := v (x.1,index x.2)
def typedPRealizer : Realizer (typedP (E:=E) (V:=V)) := pRealizer.recode
  (fun x : Context×(E×V)=>(x.1,(index x.2.1,index x.2.2))) _ (fun _=>rfl) (fun _=>rfl)
def typedQRealizer : Realizer (typedQ (E:=E)) := qRealizer.recode
  (fun x : Context×(E×E)=>(x.1,(index x.2.1,index x.2.2))) _ (fun _=>rfl) (fun _=>rfl)
def typedRRealizer : Realizer (typedR (E:=E) (V:=V)) := rRealizer.recode
  (fun x : Context×(E×(V×V))=>(x.1,(index x.2.1,(index x.2.2.1,index x.2.2.2)))) _ (fun _=>rfl) (fun _=>rfl)
def typedTRealizer : Realizer (typedT (E:=E)) := tRealizer.recode
  (fun x : Context×(E×E)=>(x.1,(index x.2.1,index x.2.2))) _ (fun _=>rfl) (fun _=>rfl)
def typedURealizer : Realizer (typedU (E:=E)) := uRealizer.recode
  (fun x : Context×E=>(x.1,index x.2)) _ (fun _=>rfl) (fun _=>rfl)
def typedVRealizer : Realizer (typedV (E:=E)) := vRealizer.recode
  (fun x : Context×E=>(x.1,index x.2)) _ (fun _=>rfl) (fun _=>rfl)
lemma polynomial_typedP : PolynomialTime (typedPRealizer (E:=E) (V:=V)) :=
  polynomial_recode _ _ _ _ polynomial_p
lemma polynomial_typedQ : PolynomialTime (typedQRealizer (E:=E)) :=
  polynomial_recode _ _ _ _ polynomial_q
lemma polynomial_typedR : PolynomialTime (typedRRealizer (E:=E) (V:=V)) :=
  polynomial_recode _ _ _ _ polynomial_r
lemma polynomial_typedT : PolynomialTime (typedTRealizer (E:=E)) :=
  polynomial_recode _ _ _ _ polynomial_t
lemma polynomial_typedU : PolynomialTime (typedURealizer (E:=E)) :=
  polynomial_recode _ _ _ _ polynomial_u
lemma polynomial_typedV : PolynomialTime (typedVRealizer (E:=E)) :=
  polynomial_recode _ _ _ _ polynomial_v

def typedDraw := pairDraw (typedP (E:=E) (V:=V)) typedQ typedR typedT typedU typedV
def typedDrawRealizer : Realizer (typedDraw (E:=E) (V:=V)) :=
  pairDrawRealizer typedPRealizer typedQRealizer typedRRealizer typedTRealizer
    typedURealizer typedVRealizer Numbered.equal Numbered.lessEqual Numbered.equal Numbered.lessEqual
lemma polynomial_typedDraw : PolynomialTime (typedDrawRealizer (E:=E) (V:=V)) :=
  polynomial_pairDraw polynomial_typedP polynomial_typedQ polynomial_typedR polynomial_typedT
    polynomial_typedU polynomial_typedV polynomial_equal polynomial_lessEqual polynomial_equal polynomial_lessEqual

lemma typedDraw_program : (typedDrawRealizer (E:=E) (V:=V)).program=drawRealizer.program := by
  simp only [typedDrawRealizer, drawRealizer, pairDrawRealizer, Realizer.congr,
    composition, pair]
  rw [draw_program ((∅,∅) : PairState E) ((∅,∅) : PairState ℕ) (by
    simp only [encode_prod,encode_empty_finset])]
  rfl

attribute [local instance] Transport.Sparse.pmOrder
lemma typedDraw_source (ends : E→Sym2 V) (hloop : ∀ e,¬(ends e).IsDiag)
    (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
    (w z : E→ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
    (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e))
    {k : ℕ} (bits : Fin k→Bool) :
    typedDraw (E:=E) (V:=V) (((contextRep ends w z,(Finset.univ,Finset.univ)),pairRepr ends a),List.ofFn bits)=
      pairRepr ends ((Transport.Sparse.pairStepTable ends hloop hpar w z hw hz a).draw k bits) := by
  exact pairDraw_eq ends hloop hpar typedP typedQ typedR typedT typedU typedV (contextRep ends w z)
    (p_rep ends w z) (q_rep ends w z) (r_rep ends w z) (t_rep ends w z) w z hw hz
    (u_rep ends w z) (v_rep ends w z) a bits
end MatchingFPRAS.ExecutablePair

end OAI
