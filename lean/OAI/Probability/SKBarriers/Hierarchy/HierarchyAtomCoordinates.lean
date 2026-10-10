import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileCDFOverlap
import OAI.Probability.SKBarriers.Scalar.ScalarSusceptibilitySum

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem hierarchyAtom_zero_coordinate (n : ℕ) (m : Fin (n+1) → ℝ) (u : ℝ) :
    hierarchyAtom (n+1) m u 0=m 0 := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    change Fin.lastCases (u-m (Fin.last (n+1)))
      (hierarchyAtom (n+1) (fun i => m i.castSucc) (m (Fin.last (n+1))))
      (0:Fin (n+1+1)).castSucc=m 0
    rw [Fin.lastCases_castSucc]
    exact ih _ _

theorem hierarchyAtom_succ_coordinate (n : ℕ) (m : Fin (n+1) → ℝ) (u : ℝ)
    (j : Fin (n+1)) : hierarchyAtom (n+1) m u j.succ=Fin.snoc (α:=fun _ => ℝ) m u j.succ-m j := by
  induction n generalizing u with
  | zero =>
    have hj : j.succ=Fin.last 1 := by ext; simp [Fin.eq_zero j]
    rw [hj]
    simp only [hierarchyAtom,Fin.lastCases_last,Fin.snoc_last,Fin.eq_zero j,Fin.last_zero]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.succ_last,hierarchyAtom,Fin.lastCases_last,Fin.snoc_last]
    · rw [← Fin.castSucc_succ]
      rw [hierarchyAtom,Fin.lastCases_castSucc,Fin.snoc_castSucc]
      rw [ih]
      congr 1
      refine Fin.lastCases ?_ (fun l => ?_) i
      · simp
      · simp only [← Fin.castSucc_succ,Fin.snoc_castSucc]

theorem hierarchyAtom_quantile_succ (k : ℕ) (j : Fin (k+1)) :
    hierarchyAtom (k+1) (quantileMass k) 1 j.succ=1/(k+1:ℕ) := by
  rw [hierarchyAtom_succ_coordinate]
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.succ_last,Fin.snoc_last,quantileMass,Fin.val_last]
    field_simp
    push_cast
    ring
  · simp only [← Fin.castSucc_succ,Fin.snoc_castSucc,quantileMass,Fin.val_succ,Fin.val_castSucc]
    push_cast
    ring

theorem monotone_quantileMass (k : ℕ) : Monotone (quantileMass k) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)

theorem finiteScalar_hessian_quantile (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) :
    rootHessian 0 (scalarHierarchy (k+1) (quantileMass k)
      (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) scalarSpinTerminal) 0=
      1-(1/(k+1:ℕ))*∑ j, quantileOverlapMean k β Q j := by
  rw [scalarHierarchy_spin_hessian_overlap_sum (k+1) _ _ (quantileMass_bounds k)
    (monotone_quantileMass k),Fin.sum_univ_succ,hierarchyAtom_zero_coordinate]
  simp only [quantileMass,Fin.val_zero,Nat.cast_zero,zero_div,zero_mul,zero_add]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hierarchyAtom_quantile_succ,quantileOverlapMean_eq_scalar]

end SK.Analytic

end
end

end OAI
