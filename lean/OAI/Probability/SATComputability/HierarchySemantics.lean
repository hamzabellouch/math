import OAI.Probability.SATComputability.HierarchyTable
import OAI.Probability.SATComputability.FiniteTrialEvaluation

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic
attribute [local irreducible] normalizedBranches branchWeights

noncomputable def leafFields (L : ℕ) (cs : List Code) : Fin L → ℝ :=
  fun i => decodedRational (cs[i.val]?.getD .zero)

theorem leafFields_ofFn {L : ℕ} (cs : Fin L → Code) :
    leafFields L (List.ofFn cs) = fun i => (decodedRational (cs i) : ℝ) := by
  funext i
  simp [leafFields, i.isLt]

theorem listLogMean_eq_finite {L : ℕ} (ms : List ℚ) (g : (Fin L → ℝ) → ℝ)
    (cs : Fin L → Code) :
    listLogMean ms (fun ds => g (leafFields L ds)) (List.ofFn cs) =
      finiteLogMean ms.length g (fun i => (ms.get i : ℝ))
        (fun i => decodeTree ms.length (cs i)) := by
  induction ms generalizing cs with
  | nil =>
    change g (leafFields L (List.ofFn cs)) = g (fun i => (decodedRational (cs i) : ℝ))
    rw [leafFields_ofFn]
  | cons m ms ih =>
    rw [listLogMean, chooseChildren_expect_ofFn]
    simp_rw [ih]
    simp only [List.length_cons, finiteLogMean, decodeTree, List.get_eq_getElem,
      List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero, Fin.val_succ]
    rw [show (instDecidableEqFin L : DecidableEq (Fin L)) =
      (fun a b => Classical.propDecidable (a = b)) from Subsingleton.elim _ _]

theorem listTrialLog_eq_finite {L : ℕ} (ms : List ℚ) (g : (Fin L → ℝ) → ℝ)
    (root : Code) :
    branchSum (chooseChildren (List.replicate L root))
      (listLogMean ms (fun ds => g (leafFields L ds))) =
        finiteTrialLog ms.length (decodeTree (ms.length+1) root)
          (fun i => (ms.get i : ℝ)) g := by
  rw [← List.ofFn_const L root, chooseChildren_expect_ofFn]
  simp_rw [listLogMean_eq_finite]
  simp only [finiteTrialLog, decodeTree]
  rw [show (instDecidableEqFin L : DecidableEq (Fin L)) =
    (fun a b => Classical.propDecidable (a = b)) from Subsingleton.elim _ _]
  rfl

end FixedClauseThreshold.Computability

end OAI
