import OAI.MathematicalPhysics.RapidForcing.NamePrograms
import OAI.MathematicalPhysics.RapidForcing.RawSyntax

namespace OAI

open Encodable Nat.Partrec
open scoped BigOperators
namespace RapidForcing
open EffectiveProfile EffectiveProfile.Formula EffectiveArithmetic

namespace EffectiveProfile.Formula
attribute [local irreducible] evalName forceFormula mixed runTyped coordinateName coordinateProgram

lemma partrec_evalCoordinates : Partrec (fun p : Formula 5 × (Program × Program) × ℚ =>
    p.1.evalName (coordinateName p.2.1.1 p.2.1.2) p.2.2) := by
  have h := partrec_evalName.comp (show Computable
    (fun p : Formula 5 × (Program × Program) × ℚ =>
      (p.1, coordinateProgram p.2.1, p.2.2)) by fun_prop)
  exact h.of_eq (fun p => by
    congr 1
    exact funext (runTyped_coordinateProgram p.2.1))

abbrev VectorArgs := (Fin 3 → Formula 5) × (Program × Program) × ℚ

def evaluateVector (p : VectorArgs) : Part RationalVector := do
  let b₀ ← (p.1 0).evalName (coordinateName p.2.1.1 p.2.1.2) (p.2.2 / 3)
  let b₁ ← (p.1 1).evalName (coordinateName p.2.1.1 p.2.1.2) (p.2.2 / 3)
  let b₂ ← (p.1 2).evalName (coordinateName p.2.1.1 p.2.1.2) (p.2.2 / 3)
  pure (b₀.center, b₁.center, b₂.center)

lemma partrec_evaluateVector : Partrec evaluateVector := by
  have h₀ := partrec_evalCoordinates.comp (show Computable (fun p : VectorArgs =>
    (p.1 0, p.2.1, p.2.2 / 3)) by fun_prop)
  have h₁ := partrec_evalCoordinates.comp (show Computable (fun p : VectorArgs × Ball =>
    (p.1.1 1, p.1.2.1, p.1.2.2 / 3)) by fun_prop)
  have h₂ := partrec_evalCoordinates.comp (show Computable (fun p : (VectorArgs × Ball) × Ball =>
    (p.1.1.1 2, p.1.1.2.1, p.1.1.2.2 / 3)) by fun_prop)
  have hf : Computable (fun p : ((VectorArgs × Ball) × Ball) × Ball =>
      (p.1.1.2.center, p.1.2.center, p.2.center)) := by fun_prop
  exact (h₀.bind (h₁.bind (h₂.bind hf.partrec.to₂).to₂).to₂).of_eq (fun _ => rfl)
end EffectiveProfile.Formula

namespace RawMachine
abbrev EvalArgs := RawInput × Program × Program × ℕ × MultiIndex × ℚ

def evaluateForce (p : EvalArgs) : Part RationalVector := do
  let q ← readPoint p.2.2.1 0
  evaluateVector (fun i => (forceFormula p.1.1 p.1.2 (timeWindow q) i).mixed p.2.2.2.1 p.2.2.2.2.1,
    (p.2.1, p.2.2.1), p.2.2.2.2.2)

attribute [local irreducible] forceFormula Formula.mixed Formula.diff Formula.bound Expr.bound
  runTyped coordinateName Formula.evalName Formula.evaluateVector

lemma computable_evalExpressions : Computable (fun p : EvalArgs × RationalPoint =>
    (fun i => (forceFormula p.1.1.1 p.1.1.2 (timeWindow p.2) i).mixed
      p.1.2.2.2.1 p.1.2.2.2.2.1)) := by
  apply computable_fin_lambda
  intro i
  have hf := computable_forceFormula.comp (show Computable
    (fun p : EvalArgs × RationalPoint => (p.1.1, timeWindow p.2)) by
      unfold timeWindow; fun_prop)
  have ha := (computable_fin_eval i).comp hf
  have hm := Formula.computable_mixed.comp (ha.pair (show Computable
    (fun p : EvalArgs × RationalPoint => (p.1.2.2.2.1, p.1.2.2.2.2.1)) by fun_prop))
  exact hm.of_eq (fun _ => rfl)

lemma partrec_evaluateForce : Partrec evaluateForce := by
  have h₀ := partrec_readPoint.comp (show Computable (fun p : EvalArgs =>
    (p.2.2.1, (0:ℕ))) by fun_prop)
  have h₁ := partrec_evaluateVector.comp (computable_evalExpressions.pair
    (show Computable (fun p : EvalArgs × RationalPoint =>
      ((p.1.2.1, p.1.2.2.1), p.1.2.2.2.2.2)) by fun_prop))
  exact (h₀.bind h₁.to₂).of_eq (fun _ => rfl)

lemma description_evaluateForce (M : Machine) (w : M.Input) (ν input : Program)
    (l : ℕ) (α : MultiIndex) (ε : ℚ) :
    evaluateForce ((M.description, w.map Fin.val), ν, input, l, α, ε) =
      Formula.evaluateForce M w ν input l α ε := by
  simp only [evaluateForce, Formula.evaluateForce, Formula.evaluateVector,
    description_forceFormula]
end RawMachine

abbrev EvalQuery := ℕ × ℕ × ℕ × ℕ × Program × ℕ
abbrev EvalParameters := RawInput × Program

noncomputable def evaluation (p : EvalParameters × EvalQuery) : Part RationalVector :=
  RawMachine.evaluateForce (p.1.1, p.1.2, p.2.2.2.2.2.1, p.2.1,
    ![p.2.2.1, p.2.2.2.1, p.2.2.2.2.1], (1/2 : ℚ)^p.2.2.2.2.2.2)

lemma partrec_evaluation : Partrec evaluation := by
  apply RawMachine.partrec_evaluateForce.comp
  apply Computable.pair (by fun_prop)
  apply Computable.pair (by fun_prop)
  apply Computable.pair (by fun_prop)
  apply Computable.pair (by fun_prop)
  apply Computable.pair
  · apply computable_fin_lambda
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  · fun_prop

noncomputable def evaluationProgram (p : EvalParameters) : Program :=
  (typedCode _ partrec_evaluation).curry (encode p)

@[fun_prop] lemma computable_evaluationProgram : Computable evaluationProgram :=
  computable_specialize.comp ((Computable.const _).pair Computable.id)

lemma evaluationProgram_eval (p : EvalParameters) (q : EvalQuery) :
    (evaluationProgram p).eval (encode q) = (evaluation (p,q)).map encode := by
  rw [evaluationProgram, Code.eval_curry, ← encode_prod_val, typedCode_eval]

@[simp] lemma evalQuery_eq (l : ℕ) (α : MultiIndex) (input : Program) (n : ℕ) :
    evalQuery l α input n = encode (l, α 0, α 1, α 2, input, n) := rfl

lemma evaluationProgram_spec (ν : ℝ) (visc : Program) (hν : NamesReal visc ν)
    (M : Machine) (w : M.Input) :
    EvaluatesMixed (evaluationProgram ((M.description, w.map Fin.val), visc)) (addressedForce ν M w) := by
  intro l α input t x ht hx n
  let ε : ℚ := (1/2)^n
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hd := Formula.evaluateForce_dom M w hν hx l α ε hε
  let r := (Formula.evaluateForce M w visc input l α ε).get hd
  have hr : r ∈ Formula.evaluateForce M w visc input l α ε := Part.get_mem hd
  refine ⟨r, ?_, ?_⟩
  · rw [evalQuery_eq, evaluationProgram_eval]
    apply Part.mem_map encode
    simpa only [evaluation, RawMachine.description_evaluateForce,
      show (![α 0, α 1, α 2] : MultiIndex) = α from by ext i; fin_cases i <;> rfl]
      using hr
  · have he := Formula.evaluateForce_spec M w hν hx ht l α ε hε hr
    simpa [ε, accuracy] using he
end RapidForcing

end OAI
