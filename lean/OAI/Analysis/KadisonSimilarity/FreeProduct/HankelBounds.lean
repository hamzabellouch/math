import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace OAI

/-!
# The finite Hankel test in the similarity manuscript

The coefficients here are the actual Fourier coefficients of the narrow-arc
function in Section `hankel`: `sin (l θ) / (π l)`, with `θ = 1/(2N)`.
The lower bound uses the constant vector in the first `N` coordinates.
No assertion about the free-product construction is assumed here.
-/

noncomputable section

namespace KadisonSimilarity

open Finset

/-- The angular half-width used in the manuscript. -/
def arcWidth (N : ℕ) : ℝ := 1 / (2 * N)

/-- A positive Fourier coefficient of the centered narrow-arc indicator. -/
def arcCoefficient (N l : ℕ) : ℝ :=
  Real.sin (l * arcWidth N) / (Real.pi * l)

theorem arcWidth_pos {N : ℕ} (hN : 0 < N) : 0 < arcWidth N := by
  unfold arcWidth
  positivity

theorem arcCoefficient_lower {N l : ℕ} (hN : 0 < N) (hl : 0 < l)
    (hlN : l < 2 * N) :
    2 * arcWidth N / Real.pi ^ 2 ≤ arcCoefficient N l := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hlNr : (l : ℝ) < 2 * N := by exact_mod_cast hlN
  have hx : 0 ≤ (l : ℝ) * arcWidth N := by
    exact mul_nonneg hlr.le (arcWidth_pos hN).le
  have hx1 : (l : ℝ) * arcWidth N < 1 := by
    unfold arcWidth
    rw [mul_one_div, div_lt_one (by positivity)]
    exact hlNr
  have hxpi : (l : ℝ) * arcWidth N ≤ Real.pi / 2 := by
    linarith [Real.pi_gt_three]
  have hs := Real.mul_le_sin hx hxpi
  unfold arcCoefficient
  apply (le_div_iff₀ (mul_pos Real.pi_pos hlr)).2
  calc
    (2 * arcWidth N / Real.pi ^ 2) * (Real.pi * l) =
        2 / Real.pi * (l * arcWidth N) := by
          field_simp
    _ ≤ Real.sin (l * arcWidth N) := hs

/-- The actual `N × N` Hankel block tested in the manuscript. -/
def arcHankelMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun j k => arcCoefficient N (j.val + k.val + 1)

theorem arcHankelMatrix_entry_lower {N : ℕ} (hN : 0 < N) (j k : Fin N) :
    2 * arcWidth N / Real.pi ^ 2 ≤ arcHankelMatrix N j k := by
  apply arcCoefficient_lower hN
  · omega
  · have := j.isLt
    have := k.isLt
    omega

/-- A finite real matrix, acting with its Hilbert-space operator norm. -/
def realMatrixOperator {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

/-- Testing on the constant vector turns a pointwise lower bound into an
operator-norm lower bound. This avoids assuming the desired Hankel estimate. -/
theorem realMatrixOperator_norm_lower {N : ℕ} (hN : 0 < N)
    (M : Matrix (Fin N) (Fin N) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hM : ∀ j k, c ≤ M j k) :
    N * c ≤ ‖realMatrixOperator M‖ := by
  let v : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun _ => 1)
  have hv : ‖v‖ ^ 2 = N := by
    simp [v, EuclideanSpace.real_norm_sq_eq]
  have hvpos : 0 < ‖v‖ := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    nlinarith [norm_nonneg v]
  have hcoord (j : Fin N) : (N : ℝ) * c ≤ realMatrixOperator M v j := by
    calc
      (N : ℝ) * c = ∑ _k : Fin N, c := by simp
      _ ≤ ∑ k : Fin N, M j k := Finset.sum_le_sum fun k _ => hM j k
      _ = realMatrixOperator M v j := by
        simp [realMatrixOperator, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, v]
  have hsum : (N : ℝ) * ((N : ℝ) * c) ^ 2 ≤ ‖realMatrixOperator M v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (N : ℝ) * ((N : ℝ) * c) ^ 2 = ∑ _j : Fin N, ((N : ℝ) * c) ^ 2 := by simp
      _ ≤ ∑ j : Fin N, (realMatrixOperator M v j) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have := hcoord j
        have : 0 ≤ (N : ℝ) * c := mul_nonneg (Nat.cast_nonneg _) hc
        nlinarith
  have hbound := (realMatrixOperator M).le_opNorm v
  have hproduct : (N : ℝ) * c * ‖v‖ ≤ ‖realMatrixOperator M v‖ := by
    have : ((N : ℝ) * c * ‖v‖) ^ 2 ≤ ‖realMatrixOperator M v‖ ^ 2 := by
      nlinarith [hsum]
    nlinarith [norm_nonneg (realMatrixOperator M v), norm_nonneg v]
  exact (mul_le_mul_iff_left₀ hvpos).1 (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hproduct.trans hbound)

/-- The finite Hankel block has the stronger lower bound `1/π²`. -/
theorem arcHankelMatrix_norm_lower {N : ℕ} (hN : 0 < N) :
    1 / Real.pi ^ 2 ≤ ‖realMatrixOperator (arcHankelMatrix N)‖ := by
  have h := realMatrixOperator_norm_lower hN (arcHankelMatrix N)
    (by have := (arcWidth_pos hN).le
        positivity : 0 ≤ 2 * arcWidth N / Real.pi ^ 2)
    (arcHankelMatrix_entry_lower hN)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  convert h using 1
  unfold arcWidth
  field_simp

/-- The weaker lower bound used for the published numerical constant. -/
theorem arcHankelMatrix_norm_lower_paper {N : ℕ} (hN : 0 < N) :
    1 / (2 * Real.pi ^ 2) ≤ ‖realMatrixOperator (arcHankelMatrix N)‖ := by
  have h := arcHankelMatrix_norm_lower hN
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have : 1 / (2 * Real.pi ^ 2) ≤ 1 / Real.pi ^ 2 := by
    apply one_div_le_one_div_of_le hp
    nlinarith
  exact this.trans h

/-- Cancellation of the nonzero corner trace in the final Hankel estimate. -/
theorem cancel_corner_trace {u x c₀ ε : ℝ} (hu : 0 < u)
    (h : u / (2 * Real.pi ^ 2) * x ≤ 3 * u * (1 + 4 * c₀) * ε) :
    x ≤ 6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε := by
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have h' := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi ^ 2)).1
    (show (u * x) / (2 * Real.pi ^ 2) ≤ 3 * u * (1 + 4 * c₀) * ε by
      simpa [div_mul_eq_mul_div] using h)
  apply (mul_le_mul_iff_right₀ hu).1
  nlinarith [h']

end KadisonSimilarity

end

end OAI
