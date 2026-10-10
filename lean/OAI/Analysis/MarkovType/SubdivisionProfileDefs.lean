import OAI.Analysis.MarkovType.OrderedSequences
import Mathlib.Data.List.OfFn

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity.Subdivision

def ofList : List ℝ → C00 :=
  @List.ofFnRec ℝ (fun _ => C00) (fun _ a => C00.ofArray a)

@[simp] theorem ofList_ofFn {m : ℕ} (a : Fin m → ℝ) :
    ofList (List.ofFn a) = C00.ofArray a := by
  exact List.ofFnRec_ofFn (C := fun _ : List ℝ => C00)
    (fun _ a => C00.ofArray a) a

def pieces (blocks : List (ℝ × ℕ)) : List ℝ :=
  blocks.flatMap fun b => List.replicate b.2 (b.1 / (b.2 : ℝ))

@[simp] theorem pieces_nil : pieces [] = [] := rfl

@[simp] theorem pieces_cons (c : ℝ) (J : ℕ) (blocks : List (ℝ × ℕ)) :
    pieces ((c, J) :: blocks) = List.replicate J (c / (J : ℝ)) ++ pieces blocks := rfl

def finiteSubdivision {m : ℕ} (a : Fin m → ℝ) (J : Fin m → ℕ) : C00 :=
  ofList (pieces (List.ofFn fun i => (a i, J i)))

end MarkovSuperreflexivity.Subdivision

end

end OAI
