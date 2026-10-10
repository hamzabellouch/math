import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeNumberedSets
import OAI.Combinatorics.MatchingCount.Sampling.TreeIndexedPairUniform
import OAI.Combinatorics.MatchingCount.Machines.TreeProgramUnique

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeTyped.SparseProgram TreeTyped.Numbered TreePost Turing

variable {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
def numericInput (x : PairInput Context E V×List Bool) : PairInput Context ℕ ℕ×List Bool :=
  (((x.1.1.1,(Numbered.set x.1.1.2.1,Numbered.set x.1.1.2.2)),
    (Numbered.set x.1.2.1,Numbered.set x.1.2.2)),x.2)
lemma numericInput_encode (x : PairInput Context E V×List Bool) : encode (numericInput x)=encode x := by
  rcases x with ⟨⟨⟨c,e,v⟩,a,b⟩,bits⟩
  simp only [numericInput,encode_prod,Numbered.encode_set]
lemma packed_draw (x : PairInput Context E V×List Bool) :
    packed (draw (numericInput x))=packed (typedDraw x) :=
  sameProgram_output drawRealizer typedDrawRealizer typedDraw_program.symm _ _ (numericInput_encode x)

theorem uniform_pair_post : ∃ p : Polynomial ℕ,
    ∀ {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
      (x : PairInput Context E V×List Bool) (t : ℕ),p.eval (packed x).length≤t →
      ∀ coins : Fin t→Bool,
      (run (machine drawRealizer.program) (packed x) coins).state=none ∧
      (run (machine drawRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (typedDraw x)) := by
  obtain ⟨p,hp⟩:=polynomial_compiles drawRealizer polynomial_draw
  refine ⟨p,fun {E V} _ _ _ _ x t ht coins=>?_⟩
  have hi:=packed_eq_of_encode (numericInput_encode x)
  have h:=hp (numericInput x) t (by simpa only [hi] using ht) coins
  simpa only [hi,packed_draw] using h

attribute [local instance] Transport.Sparse.pmOrder

theorem source_pair_post : ∃ p : Polynomial ℕ,
    ∀ {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
      (ends : E→Sym2 V) (hloop : ∀ e,¬(ends e).IsDiag)
      (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
      (w z : E→ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
      (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e))
      {k : ℕ} (bits : Fin k→Bool) (t : ℕ),
      let x := (((contextRep ends w z,((Finset.univ : Finset V),(Finset.univ : Finset E))),pairRepr ends a),List.ofFn bits)
      p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine drawRealizer.program) (packed x) coins).state=none ∧
      (run (machine drawRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (pairRepr ends ((Transport.Sparse.pairStepTable ends hloop hpar w z hw hz a).draw k bits))) := by
  obtain ⟨p,hp⟩:=uniform_pair_post
  refine ⟨p,fun {E V} _ _ _ _ ends hloop hpar w z hw hz a {k} bits t ht coins=>?_⟩
  have h:=hp (E:=E) (V:=V) (((contextRep ends w z,((Finset.univ : Finset V),(Finset.univ : Finset E))),pairRepr ends a),List.ofFn bits) t ht coins
  rwa [typedDraw_source ends hloop hpar w z hw hz a bits] at h
end MatchingFPRAS.ExecutablePair

end OAI
