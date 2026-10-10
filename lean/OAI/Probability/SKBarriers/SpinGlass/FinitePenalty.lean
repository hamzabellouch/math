import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyWeightedIncrement
import OAI.Probability.SKBarriers.Scalar.ScalarEarlyMoment

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def finiteClockPenalty (n : ℕ) (m a : Fin n → ℝ) : ℝ :=
  ∑ i, m i*((∑ j, if j < i then a j else 0)+a i)^2-
    ∑ i, m i*(∑ j, if j < i then a j else 0)^2

theorem finiteClockPenalty_eq_double (n : ℕ) (m a : Fin n → ℝ) :
    finiteClockPenalty n m a=∑ i, ∑ j, a i*a j*m (max i j) := by
  classical
  have ht (i j : Fin n) : a i*a j*m (max i j)=
      (if i < j then m j*a j*a i else 0)+
      (if j < i then m i*a i*a j else 0)+(if i=j then m i*(a i)^2 else 0) := by
    rcases lt_trichotomy i j with hij|hij|hij
    · simp only [max_eq_right (le_of_lt hij),ite_eq_left hij,
        ite_eq_right (not_lt_of_ge (le_of_lt hij)),ite_eq_right (ne_of_lt hij)]
      ring
    · subst j; simp; ring
    · simp only [max_eq_left (le_of_lt hij),ite_eq_left hij,
        ite_eq_right (not_lt_of_ge (le_of_lt hij)),ite_eq_right (ne_of_gt hij)]
      ring
  have hs : (∑ i : Fin n, ∑ j : Fin n, if i < j then m j*a j*a i else 0)=
      ∑ i : Fin n, ∑ j : Fin n, if j < i then m i*a i*a j else 0 := Finset.sum_comm
  rw [show (∑ i, ∑ j, a i*a j*m (max i j))=
      (∑ i, ∑ j, if i < j then m j*a j*a i else 0)+
      (∑ i, ∑ j, if j < i then m i*a i*a j else 0)+∑ i, m i*(a i)^2 by
    simp_rw [ht,Finset.sum_add_distrib]
    simp]
  rw [hs]
  unfold finiteClockPenalty
  rw [← Finset.sum_sub_distrib]
  have hl (i : Fin n) : m i*((∑ j, if j < i then a j else 0)+a i)^2-
      m i*(∑ j, if j < i then a j else 0)^2=
      2*(∑ j, if j < i then m i*a i*a j else 0)+m i*(a i)^2 := by
    have he : (∑ j, if j < i then m i*a i*a j else 0)=m i*a i*(∑ j, if j < i then a j else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    rw [he]; ring
  simp_rw [hl,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

theorem finiteClockPenalty_nonneg (n : ℕ) (m a : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (ha : ∀ i, 0 ≤ a i) : 0 ≤ finiteClockPenalty n m a := by
  rw [finiteClockPenalty_eq_double]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (ha i) (ha j)) (hm _)))

theorem scalarHierarchy_weighted_increment_square (n : ℕ) (m v k : Fin n → ℝ) (x : ℝ) :
    (∫ z, (coordinateLinear n (fun i => k i*v i) z)^2
      ∂hierarchyPathLaw n m (affineLogPartition (fun _ : Bool => 0)
        (fun b => spin b • scalarSpinField n v)) x)=
      (∑ i, (k i)^2*(v i)^2)+
      ∑ i, ∑ j, k i*k j*(v i)^2*(v j)^2*m (max i j)*
        scalarFiniteResponse n m v (min i j) x := by
  have hu (b : Bool) (i : Fin n) :
      (spin b • scalarSpinField n v) (coordinateAxis n i)=v i*spin b := by
    simp only [smul_apply,smul_eq_mul,scalarSpinField,
      add_apply,parameter_coordinateAxis,coordinateLinear_coordinateAxis,zero_add]
    ring
  have H := affineHierarchy_weighted_increment_square n m (fun _ : Bool => (0:ℝ))
    (fun b => spin b • scalarSpinField n v) spin v k hu x
  simp only [affineHierarchyResponse_scalar] at H
  simpa only [coordinateLinear_apply] using H

theorem scalarHierarchy_weighted_increment_square_le (n : ℕ) (m v k : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hk : ∀ i, 0 ≤ k i) (x R : ℝ)
    (hR : ∀ i, k i≠0 → scalarFiniteResponse n m v i x ≤ R) :
    (∫ z, (coordinateLinear n (fun i => k i*v i) z)^2
      ∂hierarchyPathLaw n m (affineLogPartition (fun _ : Bool => 0)
        (fun b => spin b • scalarSpinField n v)) x) ≤
      (∑ i, (k i)^2*(v i)^2)+R*finiteClockPenalty n m (fun i => k i*(v i)^2) := by
  rw [scalarHierarchy_weighted_increment_square,finiteClockPenalty_eq_double]
  refine add_le_add le_rfl ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have ha : 0 ≤ k i*k j*(v i)^2*(v j)^2*m (max i j) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hk i) (hk j)) (sq_nonneg _)) (sq_nonneg _)) (hm _)
  by_cases hi : k i=0
  · simp [hi]
  by_cases hj : k j=0
  · simp [hj]
  have H := mul_le_mul_of_nonneg_left (hR (min i j) (by
    rcases le_total i j with h|h
    · simpa only [min_eq_left h] using hi
    · simpa only [min_eq_right h] using hj)) ha
  nlinarith

end SK.Analytic

end
end

end OAI
