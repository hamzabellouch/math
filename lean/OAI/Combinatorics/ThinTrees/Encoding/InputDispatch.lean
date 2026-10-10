import Mathlib
import OAI.Combinatorics.ThinTrees.Arithmetic.WordHead
import OAI.Combinatorics.ThinTrees.Encoding.BoundaryCases
import OAI.Combinatorics.ThinTrees.Encoding.InputOutput

namespace OAI

/-! Input dispatch. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack

abbrev Good := {x : AlgorithmicThinTrees.Input // Valid x}
abbrev Large := {x : AlgorithmicThinTrees.Input // Valid x ∧ 2 ≤ x.n}
abbrev goodCode (x : Good) : Word := x.val.encode
abbrev largeCode (x : Large) : Word := x.val.encode
lemma valid_n {x : AlgorithmicThinTrees.Input} (hv : Valid x) : 1≤x.n := by
  cases x <;> exact hv.1

def isBinary : AlgorithmicThinTrees.Input → Bool
  | .explicit _ => false
  | .binary _ => true

def asBinary (x : {x : Large // isBinary x.val = true}) : B := by
  rcases x with ⟨⟨x|x,hvalid,hn⟩,hb⟩
  · cases hb
  · exact ⟨x,hn,hvalid.2⟩
def asExplicit (x : {x : Large // ¬isBinary x.val = true}) : E := by
  rcases x with ⟨⟨x|x,hvalid,hn⟩,hb⟩
  · exact ⟨x,hn,hvalid.2⟩
  · exact (hb rfl).elim

lemma asBinary_input (x : {x : Large // isBinary x.val = true}) :
    AlgorithmicThinTrees.Input.binary (asBinary x).val = x.val.val := by
  rcases x with ⟨⟨x|x,hvalid,hn⟩,hb⟩
  · cases hb
  · rfl
lemma asExplicit_input (x : {x : Large // ¬isBinary x.val = true}) :
    AlgorithmicThinTrees.Input.explicit (asExplicit x).val = x.val.val := by
  rcases x with ⟨⟨x|x,hvalid,hn⟩,hb⟩
  · rfl
  · exact (hb rfl).elim

def formatTest : Realizes largeCode boolCode (fun x => decide (isBinary x.val=true)) :=
  (wordHead.reindex largeCode largeCode (fun _ => rfl)).congr (by
    rintro ⟨x|x,h⟩ <;> rfl)
instance poly_formatTest : PolyTime formatTest := by unfold formatTest;infer_instance

def binaryTail : Realizes (fun x : {x : Large // isBinary x.val=true} => largeCode x.val)
    bCode asBinary :=
  (wordTail.reindex (fun x : {x : Large // isBinary x.val=true} => largeCode x.val)
    (fun x => largeCode x.val) (fun _ => rfl)).changeOutput bCode asBinary (by
      rintro ⟨⟨x|x,hv,hn⟩,hb⟩
      · cases hb
      · rfl)
def explicitTail : Realizes (fun x : {x : Large // ¬isBinary x.val=true} => largeCode x.val)
    eCode asExplicit :=
  (wordTail.reindex (fun x : {x : Large // ¬isBinary x.val=true} => largeCode x.val)
    (fun x => largeCode x.val) (fun _ => rfl)).changeOutput eCode asExplicit (by
      rintro ⟨⟨x|x,hv,hn⟩,hb⟩
      · rfl
      · exact (hb rfl).elim)
instance poly_binaryTail : PolyTime binaryTail := by unfold binaryTail;infer_instance
instance poly_explicitTail : PolyTime explicitTail := by unfold explicitTail;infer_instance

def largeOutput (R : ℕ) (x : Large) : Word :=
  if h : isBinary x.val=true then bOutput R (asBinary ⟨x,h⟩) else eOutput R (asExplicit ⟨x,h⟩)
def largeRun (R : ℕ) : Realizes largeCode wordCode (largeOutput R) :=
  formatTest.dite (binaryTail.then (bRun R)) (explicitTail.then (eRun R))

def makeLarge (x : {x : Good // x.val.n ≠ 1}) : Large := by
  refine ⟨x.val.val,x.val.property,?_⟩
  have hv : 1 ≤ x.val.val.n := valid_n x.val.property
  have hn := x.property
  omega

lemma makeLarge_input (x : {x : Good // x.val.n ≠ 1}) : (makeLarge x).val=x.val.val := rfl

def inputFields : AlgorithmicThinTrees.Input → List ℕ
  | .explicit x => eFields x
  | .binary x => bFields x
lemma inputFields_code (x : AlgorithmicThinTrees.Input) :
    fieldsCode (inputFields x) = x.encode.tail := by
  cases x with
  | explicit x => exact eFields_code x
  | binary x => exact bFields_code x

def goodFields : Realizes goodCode fieldsCode (fun x => inputFields x.val) :=
  (wordTail.reindex goodCode goodCode (fun _ => rfl)).changeOutput fieldsCode
    (fun x => inputFields x.val) (fun x => (inputFields_code x.val).symm)
instance poly_goodFields : PolyTime goodFields := by unfold goodFields;infer_instance

def goodN : Realizes goodCode binaryNatCode (fun x => x.val.n) :=
  (goodFields.then (field 0)).congr (by rintro ⟨x|x,h⟩ <;> rfl)
instance poly_goodN : PolyTime goodN := by unfold goodN;infer_instance

def singletonTest : Realizes goodCode boolCode (fun x => decide (x.val.n=1)) :=
  ((goodN.then binaryToRat).le (constant goodCode ratCode 1)).congr (by
    intro x
    have hn : 1 ≤ x.val.n := valid_n x.property
    simp only [Nat.cast_le_one]
    have he : (x.val.n ≤ 1) ↔ x.val.n=1 := by omega
    simp only [he])
instance poly_singletonTest : PolyTime singletonTest := by unfold singletonTest;infer_instance

def output (R : ℕ) (x : Good) : Word :=
  if h : x.val.n=1 then [] else largeOutput R (makeLarge ⟨x,h⟩)
def program (R : ℕ) : Realizes goodCode wordCode (output R) :=
  singletonTest.dite (constant (fun x : {x : Good // x.val.n=1} => goodCode x.val) wordCode [])
    ((largeRun R).reindex (fun x : {x : Good // x.val.n≠1} => goodCode x.val)
      makeLarge (fun _ => rfl))

variable {R : ℕ} {C : ℝ}
variable (hC : 0<C)
variable (hcorrect : ∀p : Problem,2≤p.d+1 → 1≤p.r → p.G.EdgeConnected p.r →
  ThinTree C p.r p.G (Iteration.tree R p.r p.G))
include hC hcorrect in
lemma largeRun_good (x : Large) : GoodOutput (2*C) x.val (largeOutput R x) := by
  unfold largeOutput
  split_ifs with h
  · rw [←asBinary_input ⟨x,h⟩]
    exact bRun_good hC hcorrect _
  · rw [←asExplicit_input ⟨x,h⟩]
    exact eRun_good hC hcorrect _
include hC hcorrect in
lemma program_good (x : Good) : GoodOutput (2*C) x.val (output R x) := by
  unfold output
  split_ifs with h
  · exact one_vertex_output _ _ h
  · exact largeRun_good hC hcorrect (makeLarge ⟨x,h⟩)

variable (htime : ∀{ι : Type} {L : ι → ℕ} (a : ι → Problem),
  IsPoly L (fun i => (problemCode (a i)).length) →
  (∀i,2 ≤ (a i).d+1 ∧ 1 ≤ (a i).r ∧ (a i).G.EdgeConnected (a i).r) →
  RunsPoly L (Iteration.Stack.treeProgram R) a)
include htime in
lemma runsPoly_largeRun {ι : Type} {L : ι → ℕ} (a : ι → Large)
    (ha : IsPoly L (fun i => (largeCode (a i)).length)) : RunsPoly L (largeRun R) a := by
  unfold largeRun
  apply RunsPoly.dite_families (RunsPoly.of_poly _ a ha)
  · have ht := RunsPoly.of_poly binaryTail (fun i : {i // isBinary (a i).val=true} =>
      ⟨a i.val,i.property⟩) (ha.reindex Subtype.val)
    exact ht.then (runsPoly_bRun htime _ ht.output)
  · have ht := RunsPoly.of_poly explicitTail (fun i : {i // ¬isBinary (a i).val=true} =>
      ⟨a i.val,i.property⟩) (ha.reindex Subtype.val)
    exact ht.then (runsPoly_eRun htime _ ht.output)
include htime in
lemma runsPoly_program {ι : Type} {L : ι → ℕ} (a : ι → Good)
    (ha : IsPoly L (fun i => (goodCode (a i)).length)) : RunsPoly L (program R) a := by
  unfold program
  apply RunsPoly.dite_families (RunsPoly.of_poly _ a ha)
  · exact RunsPoly.of_poly _ _ (ha.reindex Subtype.val)
  · apply RunsPoly.reindex
    exact runsPoly_largeRun htime _ (ha.reindex Subtype.val)

end AlgorithmicThinTrees.InputStack
end

end OAI
