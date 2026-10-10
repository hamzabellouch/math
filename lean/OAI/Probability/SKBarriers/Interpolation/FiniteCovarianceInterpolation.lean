import Mathlib
import OAI.Probability.SKBarriers.Interpolation.FiniteStatePressureCurve
import OAI.Probability.SKBarriers.Hierarchy.WeightedHierarchyProbability
import OAI.Probability.SKBarriers.Hierarchy.WeightedTerminalMean

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyAtom_nonneg_of_monotone (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hm : ∀ i, m i ∈ Icc (0:ℝ) u) (hmono : Monotone m)
    (j : Fin (n+1)) : 0 ≤ hierarchyAtom n m u j := by
  induction n generalizing u with
  | zero => exact hu
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [hierarchyAtom,Fin.lastCases_last] using sub_nonneg.mpr (hm (Fin.last n)).2
    · simp only [hierarchyAtom,Fin.lastCases_castSucc]
      apply ih _ _ (hm (Fin.last n)).1
      · intro i
        exact ⟨(hm i.castSucc).1,hmono (Fin.le_last _)⟩
      · intro i l hil
        exact hmono (by simpa using hil)

section
variable {S : Type} [Fintype S] [Nonempty S]

def partialObservableCovariance (n : ℕ) (O : Fin n → S → ℝ) (b : Fin n → ℝ)
    (j : Fin (n+1)) (s t : S) : ℝ :=
  ∑ i : Fin n, if i.val < j.val then b i*(O i s*O i t) else 0

theorem weightedCovarianceExpression_eq (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (O : Fin n → S → ℝ) (b : Fin n → ℝ) :
    (∑ i : Fin n, b i*(weightedHierarchyTerminalMean n m c U (fun s => (O i s)^2)-
      ∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*
        weightedHierarchyReplica n m c U j (fun s t => O i s*O i t) else 0)) =
      weightedHierarchyTerminalMean n m c U (fun s => ∑ i, b i*(O i s)^2)-
        ∑ j : Fin (n+1), hierarchyAtom n m 1 j*
          weightedHierarchyReplica n m c U j (partialObservableCovariance n O b j) := by
  classical
  simp only [mul_sub,Finset.sum_sub_distrib,weightedHierarchyTerminalMean_sum,
    weightedHierarchyTerminalMean_const_mul,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change _ = hierarchyAtom n m 1 j*weightedHierarchyReplica n m c U j
    (fun s t => ∑ i : Fin n, if i.val < j.val then b i*(O i s*O i t) else 0)
  rw [weightedHierarchyReplica_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val < j.val
  · simp only [ite_eq_left h,weightedHierarchyReplica_const_mul]
    ring
  · simp only [ite_eq_right h,mul_zero,weightedHierarchyReplica_const]

theorem observablePressure_hasDerivAt_covariance (n : ℕ) (O : Fin n → S → ℝ)
    (c : S → ℝ) (m : Fin n → ℝ) (a : ℝ → Fin n → ℝ) {t : ℝ} {a' : Fin n → ℝ}
    (ha : HasDerivAt a a' t) :
    HasDerivAt (fun u => hierarchyPressure n m (affineLogPartition c (observableExponent n O (a u))) 0)
      (weightedHierarchyTerminalMean n m c (observableExponent n O (a t))
        (fun s => ∑ i, (a' i*a t i)*(O i s)^2)-
      ∑ j : Fin (n+1), hierarchyAtom n m 1 j*
        weightedHierarchyReplica n m c (observableExponent n O (a t)) j
          (partialObservableCovariance n O (fun i => a' i*a t i) j)) t := by
  have H := observablePressure_hasDerivAt_curve n O c m a ha
  apply H.congr_deriv
  rw [← weightedCovarianceExpression_eq]
  simp only [weightedHierarchyTerminalMean,weightedHierarchyReplica_separable_square]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightedCovariance_bound (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (O : Fin n → S → ℝ) (b : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (D : ℝ) (C : Fin (n+1) → ℝ)
    (hdiag : ∀ s, (∑ i, b i*(O i s)^2) ≤ D)
    (hkernel : ∀ j, hierarchyAtom n m 1 j≠0 → ∀ s t, -C j ≤ partialObservableCovariance n O b j s t) :
    weightedHierarchyTerminalMean n m c U (fun s => ∑ i, b i*(O i s)^2)-
      (∑ j : Fin (n+1), hierarchyAtom n m 1 j*
        weightedHierarchyReplica n m c U j (partialObservableCovariance n O b j)) ≤
      D+∑ j : Fin (n+1), hierarchyAtom n m 1 j*C j := by
  have hD := weightedHierarchyTerminalMean_mono n m c U hdiag
  rw [weightedHierarchyTerminalMean_const] at hD
  have H : (∑ j : Fin (n+1), hierarchyAtom n m 1 j*(-C j)) ≤
      ∑ j : Fin (n+1), hierarchyAtom n m 1 j*
        weightedHierarchyReplica n m c U j (partialObservableCovariance n O b j) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : hierarchyAtom n m 1 j=0
    · simp only [hj,zero_mul,le_refl]
    · have hC := weightedHierarchyReplica_mono n m c U j (hkernel j hj)
      rw [weightedHierarchyReplica_const] at hC
      exact mul_le_mul_of_nonneg_left hC (hierarchyAtom_nonneg_of_monotone n m 1 (by norm_num) hm hmono j)
  simp only [mul_neg,Finset.sum_neg_distrib] at H
  linarith

end
end SK.Analytic

end
end

end OAI
