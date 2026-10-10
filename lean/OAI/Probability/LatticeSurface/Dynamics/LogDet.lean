import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.JacobianIdentity
import OAI.Probability.LatticeSurface.Dynamics.MatrixJacobi

namespace OAI

open Matrix Polynomial

open scoped Topology

namespace TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

open MeasureTheory

end TangentialJacobian

open Set MeasureTheory Filter

open scoped Topology

namespace TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

end TangentialJacobian

namespace TangentialJacobian

open Matrix

open scoped Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def jacobianCost (A : (V → ℝ) →L[ℝ] (V → ℝ)) : ℝ :=
  ∑ i : V, (∑ j : V, |asMatrix A i j|) * ‖A (Pi.single i 1)‖

lemma jacobianCost_nonneg (A : (V → ℝ) →L[ℝ] (V → ℝ)) : 0 ≤ jacobianCost A := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (norm_nonneg _)

lemma trace_sandwich_bound (A R : (V → ℝ) →L[ℝ] (V → ℝ)) :
    |(asMatrix (A * R * A)).trace| ≤ ‖R‖ * jacobianCost A := by
  have he (j i : V) : |asMatrix (R * A) j i| ≤ ‖R‖ * ‖A (Pi.single i 1)‖ :=
    (norm_le_pi_norm (R (A (Pi.single i 1))) j).trans (R.le_opNorm _)
  calc
    _ = |∑ i : V, ∑ j : V, asMatrix A i j * asMatrix (R * A) j i| := by
      rw [mul_assoc, asMatrix_mul]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    _ ≤ ∑ i : V, ∑ j : V, |asMatrix A i j| * |asMatrix (R * A) j i| := by
      simp_rw [← abs_mul]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : V, ∑ j : V, |asMatrix A i j| * (‖R‖ * ‖A (Pi.single i 1)‖) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_left (he j i) (abs_nonneg _)
    _ = ‖R‖ * jacobianCost A := by
      simp only [jacobianCost, ← Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring

omit [DecidableEq V] in
lemma norm_inverse_one_add_le_two (B : (V → ℝ) →L[ℝ] (V → ℝ)) (hB : ‖B‖ ≤ 1/2) :
    ‖Ring.inverse (1 + B)‖ ≤ 2 := by
  have hu : IsUnit (1 + B) := by
    simpa only [norm_neg, sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one (x := -B) (by simpa only [norm_neg] using hB.trans_lt (by norm_num : (1 : ℝ)/2 < 1) : ‖-B‖ < 1))
  have he : Ring.inverse (1 + B) = 1 - B * Ring.inverse (1 + B) := by
    have hh := Ring.mul_inverse_cancel (1 + B) hu
    rw [add_mul, one_mul] at hh
    exact eq_sub_of_add_eq hh
  have hn : ‖Ring.inverse (1 + B)‖ ≤ 1 + ‖B‖ * ‖Ring.inverse (1 + B)‖ := by
    calc
      _ = ‖1 - B * Ring.inverse (1 + B)‖ := congrArg norm he
      _ ≤ ‖(1 : (V → ℝ) →L[ℝ] (V → ℝ))‖ + ‖B * Ring.inverse (1 + B)‖ := norm_sub_le _ _
      _ ≤ 1 + ‖B‖ * ‖Ring.inverse (1 + B)‖ :=
        add_le_add ContinuousLinearMap.norm_id_le (norm_mul_le _ _)
  nlinarith [norm_nonneg (Ring.inverse (1 + B))]

lemma inverse_line_trace_identity (A : (V → ℝ) →L[ℝ] (V → ℝ)) (t : ℝ)
    (hu : IsUnit (1 + t • A)) :
    (asMatrix (Ring.inverse (1 + t • A) * A)).trace = (asMatrix A).trace -
      t * (asMatrix (A * Ring.inverse (1 + t • A) * A)).trace := by
  have he : Ring.inverse (1 + t • A) * A = A - t • (A * Ring.inverse (1 + t • A) * A) := by
    have hh := congrArg (fun B : (V → ℝ) →L[ℝ] (V → ℝ) => B * A)
      (Ring.mul_inverse_cancel (1 + t • A) hu)
    simp only [add_mul, one_mul, smul_mul_assoc] at hh
    exact eq_sub_of_add_eq hh
  rw [he, asMatrix_sub, Matrix.trace_sub, asMatrix_smul, Matrix.trace_smul, smul_eq_mul]

lemma logdet_line_deriv (A : (V → ℝ) →L[ℝ] (V → ℝ)) (t : ℝ)
    (ht : ‖t • A‖ < 1) :
    HasDerivAt (fun r : ℝ => Real.log (1 + r • A).det)
      (asMatrix (Ring.inverse (1 + t • A) * A)).trace t := by
  have hu : IsUnit (1 + t • A) := by
    simpa only [norm_neg, sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one (x := -(t • A)) (by simpa using ht))
  have hD := (det_one_add_pos (t • A) ht).ne'
  have hd := (det_line_deriv A t hu).log hD
  convert hd using 1
  field_simp

lemma logdet_lower_bound (A : (V → ℝ) →L[ℝ] (V → ℝ)) (hA : ‖A‖ ≤ 1/2) :
    (asMatrix A).trace - jacobianCost A ≤ Real.log (1 + A).det := by
  let F (t : ℝ) := Real.log (1 + t • A).det - t * (asMatrix A).trace + t^2 * jacobianCost A
  let D (t : ℝ) := (asMatrix (Ring.inverse (1 + t • A) * A)).trace - (asMatrix A).trace +
    2*t*jacobianCost A
  have hn (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖t • A‖ ≤ 1/2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg A) ht.2).trans hA
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt F (D t) t := by
    have hh := ((logdet_line_deriv A t ((hn t ht).trans_lt (by norm_num))).sub
      ((hasDerivAt_id t).mul_const (asMatrix A).trace)).add
      (((hasDerivAt_id t).pow 2).mul_const (jacobianCost A))
    convert hh using 1 <;> try rfl
    dsimp [D]
    ring
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ D t := by
    have hu : IsUnit (1 + t • A) := by
      simpa only [norm_neg, sub_neg_eq_add] using
        (isUnit_one_sub_of_norm_lt_one (x := -(t • A))
          (by simpa only [norm_neg] using (hn t ht).trans_lt (by norm_num : (1 : ℝ)/2 < 1)))
    have hb : (asMatrix (A * Ring.inverse (1 + t • A) * A)).trace ≤ 2 * jacobianCost A :=
      (le_abs_self _).trans ((trace_sandwich_bound A _).trans
        (mul_le_mul_of_nonneg_right (norm_inverse_one_add_le_two (t • A) (hn t ht)) (jacobianCost_nonneg A)))
    dsimp [D]
    rw [inverse_line_trace_identity A t hu]
    nlinarith [mul_le_mul_of_nonneg_left hb ht.1]
  have hm : MonotoneOn F (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hp t (interior_subset ht))
  have hh := hm (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num) (by norm_num)
  have h1 : (1 : (V → ℝ) →L[ℝ] (V → ℝ)).det = 1 := by simp [ContinuousLinearMap.det]
  simp only [F, zero_smul, add_zero, h1, Real.log_one, zero_mul,
    sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), one_smul, one_mul, one_pow] at hh
  linarith

end TangentialJacobian

end OAI
