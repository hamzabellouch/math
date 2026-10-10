import Mathlib
import OAI.Computability.MinUncut.Graphs.DemandExpressions

namespace OAI

noncomputable section
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.FiniteProof MinUncut.FiniteGaussian
attribute [local instance] Classical.propDecidable
variable {I Name S : Type} [Fintype I] {k m n : ℕ} {g : GridData}

def indexQuery (σ η : ℚ) (e : Index I k m n g) : Query (hiddenSet e.2.1.val) :=
  query _ e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1
    (rationalScoreTable σ η (fun i=>midpoint g.T g.L (e.2.2.2.2.2.2 i))) e.1

lemma occurrence_query (eqs : S → Equation Name) (σ η : ℚ) (u : I → S) (e : Index I k m n g) :
    elementaryQuery eqs g σ η (occurrence eqs (u,e)).1 (occurrence eqs (u,e)).2=
      (indexQuery σ η e).realize (fun i=>eqs (u i)) e.2.2.1 := by
  rcases e with ⟨j,H,pos,B,C,z,q⟩
  dsimp only [occurrence,indexQuery,elementaryQuery,localSampleEquiv,samplePull,
    Equiv.prodCongr_apply,Prod.map,Equiv.refl_apply]
  exact (query_realize _ _ _ _ _ _ _ _).symm

lemma occurrence_demand (eqs : S → Equation Name) (σ η : ℚ) (u : I → S) (e : Index I k m n g) :
    allDemand eqs g σ η (occurrence eqs (u,e))=
      ((indexQuery σ η e).realize (fun i=>eqs (u i)) e.2.2.1).signed familyBase := by
  unfold allDemand
  rw [occurrence_query]

end MinUncut.Outer.LocalTemplate

end
namespace MinUncut.Costed
lemma drop_head_append {α : Type} [Inhabited α] (xs ys : List α) (i : ℕ) (hi : i<xs.length) :
    ((xs++ys).drop i).headI=(xs.drop i).headI := by
  rw [List.drop_append_of_le_length hi.le,List.drop_eq_getElem_cons hi]
  rfl

lemma eval_pow_congr (a b : AExpr) (v w : List ℕ) (h : a.eval v=b.eval w) (i : ℕ) :
    (a.pow i).eval v=(b.pow i).eval w := by simp only [AExpr.eval_pow,h]

namespace SourceWords
open MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate

variable {t : ℕ}

lemma tuple_reg_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (i : ℕ) (hi : i<3) :
    ((inputTuple input u++rest).drop i).headI=((inputTuple input u).drop i).headI := by
  apply drop_head_append
  simp only [inputTuple,List.length_cons,SourceEncoding.inputWords_length]
  omega
lemma tupleDigit_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (j : ℕ) :
    (tupleDigit j).eval (inputTuple input u++rest)=(tupleDigit j).eval (inputTuple input u) := by
  simp only [tupleDigit,AExpr.eval,AExpr.eval_pow,tuple_reg_append input u rest 0 (by decide),
    tuple_reg_append input u rest 2 (by decide)]
lemma slotExpr_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (j : Fin t) (p : ℕ) (hp : p<4) :
    (slotExpr j.val p).eval (inputTuple input u++rest)=(slotExpr j.val p).eval (inputTuple input u) := by
  simp only [slotExpr,AExpr.eval,tupleDigit_append,tupleDigit_eval]
  apply drop_head_append
  simp only [inputTuple,List.length_cons,SourceEncoding.inputWords_length]
  have h := (u j).isLt
  omega
lemma equationExpr_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (j : Fin t) :
    (equationExpr j.val).eval (inputTuple input u++rest)=(equationExpr j.val).eval (inputTuple input u) := by
  simp (discharger := omega) only [equationExpr,AExpr.eval,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    slotExpr_append input u rest j 3 (by decide),
    slotExpr_append,AExpr.eval_pow,tuple_reg_append input u rest 1 (by decide)]
lemma firstExpr_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) :
    (firstExpr t).eval (inputTuple input u++rest)=(firstExpr t).eval (inputTuple input u) := by
  simp only [firstExpr,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,AExpr.eval,
    equationExpr_append,AExpr.eval_pow,tuple_reg_append input u rest 1 (by decide)]
lemma secondExpr_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (h : Fin t → Bool) (pos : Fin t → Fin 3) :
    (secondExpr h pos).eval (inputTuple input u++rest)=(secondExpr h pos).eval (inputTuple input u) := by
  simp only [secondExpr,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,AExpr.eval,AExpr.eval_pow,
    tuple_reg_append input u rest 1 (by decide)]
  apply Finset.sum_congr rfl
  intro j _
  cases h j <;> simp only [Bool.false_eq_true,ite_false,ite_true,AExpr.eval,equationExpr_append,
    slotExpr_append input u rest j (pos j).val (by omega),tuple_reg_append input u rest 1 (by decide)]
lemma signatureExpr_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) :
    (signatureExpr t).eval (inputTuple input u++rest)=(signatureExpr t).eval (inputTuple input u) := by
  simp (discharger := omega) only [signatureExpr,AExpr.eval,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    slotExpr_append]
lemma signatureLookup_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (f : Signature (Fin t) → ℕ) :
    (signatureLookup f).eval (inputTuple input u++rest)=(signatureLookup f).eval (inputTuple input u) := by
  simp only [signatureLookup,AExpr.eval_lookup,signatureExpr_append]
lemma secondAddress_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (h : Fin t → Bool) (pos : Fin t → Fin 3) :
    (secondAddress h pos).eval (inputTuple input u++rest)=(secondAddress h pos).eval (inputTuple input u) := by
  simp only [secondAddress,AExpr.eval,AExpr.eval_pow,tuple_reg_append input u rest 1 (by decide),secondExpr_append]
lemma queryWords_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) {h : Fin t → Bool} (T : Query h) (pos : Fin t → Fin 3) :
    queryWords T pos (inputTuple input u++rest)=queryWords T pos (inputTuple input u) := by
  simp only [queryWords,leftExpr,rightExpr,signExpr,AExpr.eval,signatureLookup_append,secondAddress_append]
  cases T.first <;> simp only [Bool.false_eq_true,ite_false,ite_true,firstExpr_append,secondAddress_append]
end SourceWords
end MinUncut.Costed

end OAI
