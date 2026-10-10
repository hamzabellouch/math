import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.ArithmeticSize
import OAI.Combinatorics.MatchingCount.Tapes.StackLens
import OAI.Combinatorics.MatchingCount.Tapes.WordOps

namespace OAI

namespace MatchingFPRAS.RegisterProc
open Turing MachineCost

abbrev Store := Option Bool
abbrev Stack (K : Type) := K → List Bool
structure Proc (K : Type) where
  Label : Type
  [labels : Fintype Label]
  [entry : Inhabited Label]
  code : Label → TM2.Stmt (fun _ : K=>Bool) Label Store
attribute [instance] Proc.labels Proc.entry
variable {K : Type} [DecidableEq K]

def Exec (P : Proc K) (S T : Stack K) (bound : ℕ) : Prop :=
  ∃ n≤bound,MachineCost.run (TM2.step P.code) n ⟨some default,none,S⟩=⟨none,none,T⟩
lemma Exec.mono {P : Proc K} {S T : Stack K} {n m : ℕ}
    (h : Exec P S T n) (hn : n ≤ m) : Exec P S T m := by
  obtain ⟨k,hk,he⟩:=h; exact ⟨k,hk.trans hn,he⟩

def seq (P Q : Proc K) : Proc K :=
  { Label := P.Label ⊕ Q.Label
    entry := ⟨Sum.inl default⟩
    code := StackComposition.sequence P.code Q.code }
lemma Exec.seq {P Q : Proc K} {S T U : Stack K} {n m : ℕ}
    (hP : Exec P S T n) (hQ : Exec Q T U m) : Exec (seq P Q) S U (n+m) := by
  obtain ⟨i,hi,he⟩:=hP
  obtain ⟨j,hj,hf⟩:=hQ
  obtain ⟨k,hk,hg⟩:=StackComposition.sequence_run P.code Q.code
    ⟨some default,none,S⟩ i j none none T U he hf
  exact ⟨k,hk.trans (Nat.add_le_add hi hj),hg⟩

def atom (s : TM2.Stmt (fun _ : K=>Bool) Unit Store) : Proc K := ⟨Unit,fun _=>s⟩
lemma exec_atom (s : TM2.Stmt (fun _ : K=>Bool) Unit Store) (S T : Stack K)
    (h : TM2.stepAux s none S=⟨none,none,T⟩) : Exec (atom s) S T 1 := ⟨1,le_rfl,h⟩

def reindex (P : Proc (Fin 3)) (e : Fin 3 ↪ K) : Proc K :=
  ⟨P.Label,StackLens.program e (StackLens.Lens.identity Store) P.code⟩
noncomputable def frame (e : Fin 3 ↪ K) (A B C : List Bool) (S : Stack K) : Stack K :=
  StackEmbedding.extend e ![A,B,C] S
lemma exec_reindex (P : Proc (Fin 3)) (e : Fin 3 ↪ K) (S : Stack K)
    (A B C A' B' C' : List Bool) (n : ℕ)
    (h : Exec P ![A,B,C] ![A',B',C'] n) :
    Exec (reindex P e) (frame e A B C S) (frame e A' B' C' S) n := by
  obtain ⟨k,hk,he⟩:=h
  refine ⟨k,hk,?_⟩
  have hh := StackLens.run_cfg e (StackLens.Lens.identity Store) P.code S none k
    ⟨some default,none,![A,B,C]⟩
  rw [he] at hh
  exact hh

def triple (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) : Fin 3 ↪ K :=
  ⟨![a,b,c],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
omit [DecidableEq K] in
@[simp] lemma triple_zero (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    triple a b c hab hac hbc 0=a := rfl
omit [DecidableEq K] in
@[simp] lemma triple_one (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    triple a b c hab hac hbc 1=b := rfl
omit [DecidableEq K] in
@[simp] lemma triple_two (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    triple a b c hab hac hbc 2=c := rfl

def put3 (S : Stack K) (a b c : K) (A B C : List Bool) : Stack K :=
  Function.update (Function.update (Function.update S a A) b B) c C
lemma frame_triple (S : Stack K) (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (A B C : List Bool) : frame (triple a b c hab hac hbc) A B C S=put3 S a b c A B C := by
  funext j
  by_cases hja : j=a
  · subst j
    have hh:=StackEmbedding.extend_on (triple a b c hab hac hbc) ![A,B,C] S 0
    simpa [frame,put3,hab,hac,hbc,hab.symm,hac.symm,hbc.symm] using hh
  by_cases hjb : j=b
  · subst j
    have hh:=StackEmbedding.extend_on (triple a b c hab hac hbc) ![A,B,C] S 1
    simpa [frame,put3,hab,hac,hbc,hab.symm,hac.symm,hbc.symm] using hh
  by_cases hjc : j=c
  · subst j
    have hh:=StackEmbedding.extend_on (triple a b c hab hac hbc) ![A,B,C] S 2
    simpa [frame,put3] using hh
  have he : ¬∃ k,triple a b c hab hac hbc k=j := by
    rintro ⟨k,hk⟩; fin_cases k <;> simp_all
  rw [frame,StackEmbedding.extend_off _ _ _ j he]
  simp [put3,hja,hjb,hjc]
lemma put3_same (S : Stack K) (a b c : K) (_ : a≠b) (hac : a≠c) (hbc : b≠c) :
    put3 S a b c (S a) (S b) (S c)=S := by
  funext j
  by_cases hja : j=a <;> by_cases hjb : j=b <;> by_cases hjc : j=c <;> simp_all [put3]

def clearRaw : Proc (Fin 3) := ⟨Unit,WordOps.clear⟩
def reverseRaw : Proc (Fin 3) := ⟨Unit,StackReverse.program⟩
def duplicateRaw : Proc (Fin 3) := ⟨Unit,WordOps.duplicate⟩
def transferRaw : Proc (Fin 3) := ⟨Unit,TreeTransfer.program⟩
lemma clearRaw_exec (A B C : List Bool) :
    Exec clearRaw ![A,B,C] ![[],B,C] (A.length+1) :=
  ⟨_,le_rfl,WordOps.run_clear A B C none⟩
lemma reverseRaw_exec (A B C : List Bool) :
    Exec reverseRaw ![A,B,C] ![[],A.reverse++B,C] (A.length+1) :=
  ⟨_,le_rfl,StackReverse.run_reverse A B C none⟩
lemma duplicateRaw_exec (A B C : List Bool) :
    Exec duplicateRaw ![A,B,C] ![[],A.reverse++B,A.reverse++C] (A.length+1) :=
  ⟨_,le_rfl,WordOps.run_duplicate A B C none⟩
lemma transferRaw_exec (x : TreeData.Data) (A B : List Bool) :
    Exec transferRaw ![TreeData.encode x++A,B,[false]] ![A,(TreeData.encode x).reverse++B,[]]
      ((TreeData.encode x).length+1) :=
  ⟨_,le_rfl,TreeTransfer.run_transfer x A B none⟩
end MatchingFPRAS.RegisterProc

end OAI
