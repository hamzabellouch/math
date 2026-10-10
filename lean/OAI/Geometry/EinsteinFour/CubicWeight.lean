import OAI.Geometry.EinsteinFour.BianchiCubic
import OAI.Geometry.EinsteinFour.MatrixSlotCubic

namespace OAI

/-! Normalize the actual cubic trace and its squared-weight contribution. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open TraceHessian

noncomputable section

/-- The matrix of derivatives in a fixed tangent direction. -/
def derivativeMatrix (T : Tensor) (d : Fin 4) : Mat :=
  fun i j => T.matrix i j d

theorem derivativeMatrix_symmetric (T : Tensor) (d : Fin 4) :
    symmetric (derivativeMatrix T d) := by
  intro i j
  exact congrArg (fun q : Vec => q d) (T.matrix_symmetric i j)

/-- The trace appearing in the varying matrix-slot coefficient. -/
def weightedCubicTrace (a : Vec) (T : Tensor) : ℝ :=
  ∑ d, a d * Matrix.trace (derivativeMatrix T d *
    (∑ j, derivativeMatrix T j * derivativeMatrix T j))

private theorem derivative_trace (T : Tensor) (d : Fin 4) :
    Matrix.trace (derivativeMatrix T d *
      (∑ j, derivativeMatrix T j * derivativeMatrix T j)) =
      ∑ i, ∑ j, ∑ k, T.matrix i j d * inner ℝ (T.matrix j k) (T.matrix k i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sum_apply,
    derivativeMatrix, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro d' _
  ring

/-- The coordinate contraction and the actual matrix trace have exactly
the normalization used in the weighted Green formula. -/
theorem weightedCubicTrace_eq (a : Vec) (T : Tensor) :
    weightedCubicTrace a T = 6 * cubicContraction a T := by
  unfold weightedCubicTrace
  simp_rw [derivative_trace]
  simp only [Finset.mul_sum]
  calc
    _ = ∑ i : Fin 3, ∑ d : Fin 4, ∑ j : Fin 3, ∑ k : Fin 3,
        a d * (T.matrix i j d * inner ℝ (T.matrix j k) (T.matrix k i)) :=
      Finset.sum_comm
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ d : Fin 4,
        a d * (T.matrix i j d * inner ℝ (T.matrix j k) (T.matrix k i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        inner ℝ a (T.matrix i j) * inner ℝ (T.matrix j k) (T.matrix k i) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      have ha : inner ℝ a (T.matrix i j) = ∑ d, a d * T.matrix i j d := by
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
        apply Finset.sum_congr rfl
        intro d _
        ring
      rw [ha, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := by unfold cubicContraction; ring

theorem cubicContraction_smul (r : ℝ) (a : Vec) (T : Tensor) :
    cubicContraction (r • a) T = r * cubicContraction a T := by
  simp only [cubicContraction, real_inner_smul_left, mul_assoc,
    ← Finset.mul_sum]
  ring

theorem cubicContraction_zero (T : Tensor) : cubicContraction 0 T = 0 := by
  simp [cubicContraction]

/-- The sharp diagonal-frame estimate applies to every actual Bianchi
tensor, by the proved reconstruction of its three vector coordinates. -/
theorem cubicContraction_sharp_tensor_diagonal (S : Shape) (a : Vec) (T : Tensor)
    (ht : T.traceFree) (hb : T.bianchi) {ν : ℝ}
    (ha : ‖a‖ = 1) (hν : 0 ≤ ν)
    (hdiag : ∀ i j, inner ℝ a (T.matrix i j) = if i = j then ν * S.s i else 0) :
    |cubicContraction a T| ≤
      (4 / 5) * Real.sqrt (3 / 5) * (T.squaredNorm / 6) *
        Real.sqrt (T.squaredNorm / 6) := by
  have hrec := parameters_reconstruction S T ht hb
  rw [← hrec] at hdiag ⊢
  exact cubicContraction_sharp_diagonal S a _ _ _ ha hν hdiag

/-- Homogeneity gives the sharp contraction for a non-unit distinguished
direction once its normalized diagonal frame has been supplied. -/
theorem cubicContraction_sharp_scaled_diagonal (S : Shape) (a : Vec) (T : Tensor)
    (ht : T.traceFree) (hb : T.bianchi) (r : ℝ) {ν : ℝ}
    (ha : ‖a‖ = 1) (hν : 0 ≤ ν)
    (hdiag : ∀ i j, inner ℝ a (T.matrix i j) = if i = j then ν * S.s i else 0) :
    |cubicContraction (r • a) T| ≤
      ‖r • a‖ * ((4 / 5) * Real.sqrt (3 / 5) * (T.squaredNorm / 6) *
        Real.sqrt (T.squaredNorm / 6)) := by
  rw [cubicContraction_smul, abs_mul, norm_smul, ha, mul_one, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (cubicContraction_sharp_tensor_diagonal S a T ht hb ha hν hdiag) (abs_nonneg r)

/-- The coefficient `−5/36` in the collected Hessian formula multiplies
the full trace, giving exactly the positive cubic term in equation (19).
The sharp directional estimate remains an explicit local obligation. -/
theorem squared_weight_cubic_bound (T : Tensor) (M : ℝ) (hM : 0 ≤ M)
    (p q : Vec)
    (hsharp : |cubicContraction ((-(3 / 4 : ℝ) * M) • (p - q)) T| ≤
      ‖(-(3 / 4 : ℝ) * M) • (p - q)‖ *
        ((4 / 5) * Real.sqrt (3 / 5) * (T.squaredNorm / 6) *
          Real.sqrt (T.squaredNorm / 6))) :
    -(5 / 36 : ℝ) * weightedCubicTrace ((-(3 / 4 : ℝ) * M) • (p - q)) T ≤
      (1 / 2 : ℝ) * Real.sqrt (3 / 5) * (‖p‖ + ‖q‖) * M *
        ((T.squaredNorm / 6) * Real.sqrt (T.squaredNorm / 6)) := by
  have he : 0 ≤ T.squaredNorm / 6 := by
    unfold Tensor.squaredNorm
    positivity
  have hnorm : ‖(-(3 / 4 : ℝ) * M) • (p - q)‖ ≤
      (3 / 4 : ℝ) * M * (‖p‖ + ‖q‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hM]
    norm_num
    exact mul_le_mul_of_nonneg_left (norm_sub_le p q) (by positivity)
  have hc : 0 ≤ (4 / 5 : ℝ) * Real.sqrt (3 / 5) * (T.squaredNorm / 6) *
      Real.sqrt (T.squaredNorm / 6) := by positivity
  have hu := hsharp.trans (mul_le_mul_of_nonneg_right hnorm hc)
  have hlo := (abs_le.mp hu).1
  rw [weightedCubicTrace_eq]
  nlinarith only [hlo]

end
end PositiveEinsteinFour.Bianchi

end OAI
