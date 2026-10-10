import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeProgramUnique
import OAI.Combinatorics.MatchingCount.Sampling.TreeLadderIndexed

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered ExecutableLadder TreePost Turing

variable {I : Type} [Fintype I] [LinearOrder I] [Inhabited I]
def numericSetup (x : RunSetup Context I ℕ) : RunSetup Context ℕ ℕ :=
  ((x.1.1,(Numbered.set x.1.2.1,Numbered.set x.1.2.2)),(x.2.1.map index,x.2.2))
def numericState (x : StateTable I (Finset ℕ)) : StateTable ℕ (Finset ℕ) := x.map (fun a=>(index a.1,a.2))
def numericInput (x : TypedInput I) : Input := (x.1,(numericSetup x.2.1,numericState x.2.2))
omit [Inhabited I] in
lemma encode_indices (xs : List I) : encode (xs.map index)=encode xs := by
  induction xs with
  | nil=>rfl
  | cons a as ih=>simp only [List.map_cons,encode_list_cons,ih]; rfl
omit [Inhabited I] in
lemma numericState_encode (x : StateTable I (Finset ℕ)) : encode (numericState x)=encode x := by
  induction x with
  | nil=>rfl
  | cons a as ih=>
    change TreeData.Data.cons (encode (index a.1,a.2)) (encode (numericState as))=TreeData.Data.cons (encode a) (encode as)
    rw [ih]
    rfl
omit [Inhabited I] in
lemma numericInput_encode (x : TypedInput I) : encode (numericInput x)=encode x := by
  rcases x with ⟨bits,⟨⟨c,u,b⟩,keys,e⟩,s⟩
  simp only [numericInput,numericSetup,encode_prod,Numbered.encode_set,encode_indices,numericState_encode]
lemma packed_execute (hz : index (default : I)=0) (x : TypedInput I) :
    packed (execute (numericInput x))=packed (typedExecute x) :=
  sameProgram_output executeRealizer typedExecuteRealizer (typedExecute_program hz).symm _ _ (numericInput_encode x)

theorem uniform_ladder_post : ∃ p : Polynomial ℕ,
    ∀ {I : Type} [Fintype I] [LinearOrder I] [Inhabited I], index (default : I)=0 →
      ∀ (x : TypedInput I) (t : ℕ),p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine executeRealizer.program) (packed x) coins).state=none ∧
      (run (machine executeRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (typedExecute x)) := by
  obtain ⟨p,hp⟩:=polynomial_compiles executeRealizer polynomial_execute
  refine ⟨p,fun {I} _ _ _ hz x t ht coins=>?_⟩
  have hi:=packed_eq_of_encode (numericInput_encode x)
  have h:=hp (numericInput x) t (by simpa only [hi] using ht) coins
  simpa only [hi,packed_execute hz] using h
end MatchingFPRAS.NumericLadder

end OAI
