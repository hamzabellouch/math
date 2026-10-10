import OAI.Computability.MatchingCount.RawOddBounds

namespace OAI

section

namespace BinaryMatching.Raw
open StackCode RecursiveEval

def rawTotal (c : Matrix ℕ) : ℕ := c.flatten.sum
lemma rawTotal_rep {n : ℕ} (c : Fin n → Fin n → ℕ) : rawTotal (matrixRep c)=DenseOracle.total c := by
  simp only [rawTotal,matrixRep,vectorRep,List.sum_flatten,List.map_ofFn,List.sum_ofFn,DenseOracle.total,Function.comp_def]

def oddFlat (z : ℕ×(Matrix ℕ×Cut)) : Cut :=
  let s := ((guardedStep (paramStep empty oddExpand oddCombine))^[2*z.1]
    (oddBudget z.1 (rawTotal z.2.1),(z.1,([Command.call (cardinal z.2.2) (z.2.1,z.2.2)],[])))).2
  s.2.2.headD []

theorem oddFlat_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n))
    (he : Even U.card) (hU : 2≤U.card) :
    oddFlat (n,(matrixRep c,cutRep U))=cutRep (OddMincut.oddCut c U) := by
  unfold oddFlat
  simp only [rawTotal_rep,cardinal_rep]
  rw [guardedStep_eq (paramStep empty oddExpand oddCombine)
    (oddBudget n (DenseOracle.total c)) (n,([Command.call U.card (matrixRep c,cutRep U)],[])) (2*n)
    (fun j hj => oddOrbit_bound c U _ le_rfl j hj)]
  rw [paramStep_iterate]
  rw [runs_extra (empty n) (oddExpand n) (oddCombine n) U.card
    (matrixRep c,cutRep U) (2*n) (oddCost_bound c U he hU)]
  exact oddValue_rep _ c U

namespace Compiler
open StackCode.Poly RecursiveEval.Compile
@[fun_prop] theorem rawTotal_poly : Poly rawTotal := by unfold rawTotal; fun_prop
@[fun_prop] theorem oddBudget_poly : Poly (fun z : ℕ×ℕ => oddBudget z.1 z.2) := by unfold oddBudget; fun_prop
@[fun_prop] theorem oddExpand_poly : Poly (fun z : ℕ×OddArg => oddExpand z.1 z.2) := by
  let A (z : ℕ×OddArg) := terminalCut z.1 z.2.1 z.2.2
  have hA : Poly A := terminalCut_poly
  have h : Poly (fun z : ℕ×OddArg =>
      if decide (cardinal (inter z.1 (A z) z.2.2)%2=1) then Branch.leaf (A z) else
      if (outside z.1 (A z)).isSome && (outside z.1 (compl z.1 (A z))).isSome then
        Branch.fork (z.2.1,(A z,((outside z.1 (A z)).getD 0,(outside z.1 (compl z.1 (A z))).getD 0)))
          (contract z.1 z.2.1 (A z) ((outside z.1 (A z)).getD 0),inter z.1 (A z) z.2.2)
          (contract z.1 z.2.1 (compl z.1 (A z)) ((outside z.1 (compl z.1 (A z))).getD 0),inter z.1 (compl z.1 (A z)) z.2.2)
      else Branch.leaf (empty z.1) : (ℕ×OddArg) → Branch OddArg Cut OddJoin) := by fun_prop
  exact h.congr (fun z => by
    unfold oddExpand
    dsimp only [A]
    simp only [decide_eq_true_eq]
    by_cases hp : cardinal (inter z.1 (terminalCut z.1 z.2.1 z.2.2) z.2.2)%2=1
    · simp only [ite_eq_left hp]
    · simp only [ite_eq_right hp]
      cases outside z.1 (terminalCut z.1 z.2.1 z.2.2) <;>
        cases outside z.1 (compl z.1 (terminalCut z.1 z.2.1 z.2.2)) <;> rfl)
@[fun_prop] theorem oddCombine_poly : Poly (fun z : ℕ×(OddJoin×(Cut×Cut)) => oddCombine z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold oddCombine
  fun_prop
@[fun_prop] theorem oddFlat_poly : Poly oddFlat := by
  have hs := paramStep_poly empty oddExpand oddCombine rawEmpty oddExpand_poly oddCombine_poly
  have hg := Poly.guardedIterate (paramStep empty oddExpand oddCombine) hs
  have hi := Poly.comp _ (fun z : ℕ×(Matrix ℕ×Cut) =>
    (2*z.1,(oddBudget z.1 (rawTotal z.2.1),(z.1,([Command.call (cardinal z.2.2) (z.2.1,z.2.2)],[]))))) hg (by fun_prop)
  exact Poly.comp (fun s : ℕ×State OddArg Cut OddJoin => s.2.2.headD []) _ (by fun_prop) hi
end Compiler
end BinaryMatching.Raw
end

end OAI
