import OAI.NumberTheory.Ostmann.Characters.TemplateLeafSymbolic
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalHeightDenominator

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
open SymbolicHistory
variable {ι : Type*}

def obstructionExpressions (k j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) : List (Expr ι) :=
  pivotExpressions k j s e t ++
    (bottomExpressions k j b s e t).map (fun q => periodExpression k q.2.2)

theorem obstructionExpressions_good (k : ℕ) (B V : (j:ℕ) → State k (j+1) → ℤ) (j : ℕ)
    (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (a : ι → ℤ) (he : ∀ u, HistoryReconstruction.Good a (e u))
    (h : Supported k B V j s (evalExpressions a e) t) :
    ∀ q ∈ obstructionExpressions k j b s e t, HistoryReconstruction.Good a q := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact pivotExpressions_good k B V j s e t a he h q hq
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
    exact finiteProductExpression_good v.2.2 a
      (bottomExpressions_good k B V j b s e t a he h v hv)

end Ostmann.Characters.Template

end

end OAI
