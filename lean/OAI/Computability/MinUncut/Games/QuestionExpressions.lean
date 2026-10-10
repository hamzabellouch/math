import Mathlib
import OAI.Computability.MinUncut.Games.QuestionArithmetic

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Reduction MinUncut.SourceBridge

variable {t : ℕ}

def tupleDigit (j : ℕ) : AExpr := .mod (.div (.reg 0) ((AExpr.reg 2).pow j)) (.reg 2)
def slotExpr (j p : ℕ) : AExpr := .at (.add (.add (.const 3) (.mul (.const 4) (tupleDigit j))) (.const p))
def inputTuple (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) : List ℕ :=
  (finFunctionFinEquiv u).val::SourceEncoding.inputWords input

lemma tupleDigit_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) (j : Fin t) :
    (tupleDigit j.val).eval (inputTuple input u)=(u j).val := by
  have hh := congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply u) j)
  change (finFunctionFinEquiv u).val/input.equations.length^j.val%input.equations.length=(u j).val at hh
  simpa only [tupleDigit,AExpr.eval,AExpr.eval_pow,inputTuple,SourceEncoding.inputWords,
    List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.headI_cons] using hh

lemma slotExpr_name (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) (j : Fin t) (p : Fin 3) :
    (slotExpr j.val p.val).eval (inputTuple input u)=((equations input (u j)).names p).val := by
  simp only [slotExpr,AExpr.eval,tupleDigit_eval]
  have he : 3+4*(u j).val+p.val=(2+4*(u j).val+p.val)+1 := by omega
  rw [he]
  exact input_name input (u j) p

lemma slotExpr_rhs (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) (j : Fin t) :
    (slotExpr j.val 3).eval (inputTuple input u)=(equations input (u j)).rhs.val := by
  simp only [slotExpr,AExpr.eval,tupleDigit_eval]
  have he : 3+4*(u j).val+3=(2+4*(u j).val+3)+1 := by omega
  rw [he]
  exact input_rhs input (u j)

def equationExpr (j : ℕ) : AExpr := .add (slotExpr j 3) (.mul (.const 2)
  (AExpr.sum (List.ofFn (fun p : Fin 3=>.mul (slotExpr j p.val) ((AExpr.reg 1).pow p.val)))))

def firstExpr (t : ℕ) : AExpr := AExpr.sum (List.ofFn (fun i : Fin t=>
  .mul (equationExpr i.val) ((AExpr.mul ((AExpr.reg 1).pow 3) (.const 2)).pow i.val)))

def secondExpr {t : ℕ} (h : Fin t → Bool) (pos : Fin t → Fin 3) : AExpr :=
  AExpr.sum (List.ofFn (fun i : Fin t=>
    .mul (if h i then slotExpr i.val (pos i).val else .add (.reg 1) (equationExpr i.val))
      ((AExpr.add (.reg 1) (.mul ((AExpr.reg 1).pow 3) (.const 2))).pow i.val)))

lemma reg1_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) :
    (AExpr.reg 1).eval (inputTuple input u)=input.«variables» := rfl

lemma inputTuple_reg1 (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) :
    ((inputTuple input u).drop 1).headI=input.«variables» := rfl

lemma equationExpr_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) (j : Fin t) :
    (equationExpr j.val).eval (inputTuple input u)=equationNumber (equations input (u j)) := by
  simp only [equationExpr,AExpr.eval,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    slotExpr_rhs,slotExpr_name,AExpr.eval_pow,inputTuple_reg1,equationNumber]

lemma firstExpr_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) :
    (firstExpr t).eval (inputTuple input u)=firstNumber (fun j=>equations input (u j)) := by
  simp only [firstExpr,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,AExpr.eval,
    equationExpr_eval,AExpr.eval_pow,inputTuple_reg1,firstNumber]

lemma secondExpr_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (h : Fin t → Bool) (pos : Fin t → Fin 3) :
    (secondExpr h pos).eval (inputTuple input u)=secondNumber (fun j=>equations input (u j)) h pos := by
  simp only [secondExpr,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,AExpr.eval,AExpr.eval_pow,
    inputTuple_reg1,secondNumber]
  apply Finset.sum_congr rfl
  intro j _
  cases h j <;> simp only [Bool.false_eq_true,ite_false,ite_true,AExpr.eval,equationExpr_eval,slotExpr_name,inputTuple_reg1]

end MinUncut.Costed.SourceWords

end
end

end OAI
