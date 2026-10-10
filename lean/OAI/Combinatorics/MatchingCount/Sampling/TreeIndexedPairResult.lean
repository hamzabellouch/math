import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeIndexedPairPost
import OAI.Combinatorics.MatchingCount.Tapes.TreeEncodingInjective

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeTyped.Numbered TreeTyped.SparseProgram TreePost

variable {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
lemma numeric_draw (x : PairInput Context E V×List Bool) :
    draw (numericInput x)=(Numbered.set (typedDraw x).1,Numbered.set (typedDraw x).2) := by
  apply pair_encode_injective finsetNat_encode_injective finsetNat_encode_injective
  have h:=sameProgram_encode drawRealizer typedDrawRealizer typedDraw_program.symm _ _ (numericInput_encode x)
  have he : encode (Numbered.set (typedDraw x).1,Numbered.set (typedDraw x).2)=encode (typedDraw x) :=
    congrArg₂ TreeData.Data.cons (Numbered.encode_set _) (Numbered.encode_set _)
  exact h.trans he.symm
attribute [local instance] Transport.Sparse.pmOrder
lemma numeric_draw_source (ends : E→Sym2 V) (hloop : ∀ e,¬(ends e).IsDiag)
    (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
    (w z : E→ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
    (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e))
    {k : ℕ} (bits : Fin k→Bool) :
    draw ((((contextRep ends w z,(Numbered.set (Finset.univ : Finset V),Numbered.set (Finset.univ : Finset E))),
      (Numbered.set a.1.val,Numbered.set a.2.val)),List.ofFn bits))=
      (Numbered.set ((Transport.Sparse.pairStepTable ends hloop hpar w z hw hz a).draw k bits).1.val,
       Numbered.set ((Transport.Sparse.pairStepTable ends hloop hpar w z hw hz a).draw k bits).2.val) := by
  have h:=numeric_draw (E:=E) (V:=V) (((contextRep ends w z,(Finset.univ,Finset.univ)),pairRepr ends a),List.ofFn bits)
  rw [typedDraw_source ends hloop hpar w z hw hz a bits] at h
  exact h
end MatchingFPRAS.ExecutablePair

end OAI
