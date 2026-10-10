import OAI.Geometry.EinsteinFour.WeylLaplacian
import OAI.Geometry.EinsteinFour.BianchiCurvatureProjection

namespace OAI

/-! Bilinear matrix-slot compression on two actual Bianchi gradients. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

private def addTensor (Z W : Tensor) : Tensor where
  diagonal a := Z.diagonal a + W.diagonal a
  off a := Z.off a + W.off a

private theorem addTensor_matrix (Z W : Tensor) :
    (addTensor Z W).matrix = Z.matrix + W.matrix := by
  funext a b
  fin_cases a <;> fin_cases b <;> rfl

private theorem addTensor_traceFree (Z W : Tensor)
    (hz : Z.traceFree) (hw : W.traceFree) : (addTensor Z W).traceFree := by
  change (∑ a, (Z.diagonal a + W.diagonal a)) = 0
  rw [Finset.sum_add_distrib, hz, hw, add_zero]

private theorem addTensor_bianchi (Z W : Tensor)
    (hz : Z.bianchi) (hw : W.bianchi) : (addTensor Z W).bianchi := by
  intro i
  rw [Tensor.divergence_eq_sum]
  simp only [addTensor_matrix, Pi.add_apply, quaternion_add, Finset.sum_add_distrib,
    ← Tensor.divergence_eq_sum, hz i, hw i, add_zero]

/-- Polarization of the exact generator norm identity. -/
theorem generator_row_pairing (s : Fin 3) (Z W : Tensor)
    (hz : Z.traceFree) (hbz : Z.bianchi) (hw : W.traceFree) (hbw : W.bianchi) :
    rawPairing (rawGradientGenerator s Z.matrix) (rawGradientGenerator s W.matrix) +
      40 * (∑ b, inner ℝ (Z.matrix s b) (W.matrix s b)) =
        25 * rawPairing Z.matrix W.matrix := by
  have h := generator_row_energy s (addTensor Z W)
    (addTensor_traceFree Z W hz hw) (addTensor_bianchi Z W hbz hbw)
  have hZ := generator_row_energy s Z hz hbz
  have hW := generator_row_energy s W hw hbw
  simp only [Tensor.squaredNorm, addTensor_matrix, rawGradientGenerator_add,
    Pi.add_apply, norm_add_sq_real, Finset.sum_add_distrib,
    ← Finset.mul_sum] at h
  rw [rawPairing_vectors, rawPairing_vectors]
  simp only [Tensor.squaredNorm] at hZ hW
  linear_combination (1 / 2 : ℝ) * (h - hZ - hW)

/-- The diagonal matrix-slot form keeps both Bianchi arguments. -/
def diagonalGradientPairing (t : Fin 3 → ℝ) (Z W : Tensor) : ℝ :=
  ∑ s, t s * (∑ b, inner ℝ (Z.matrix s b) (W.matrix s b))

theorem weighted_generator_pairing (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (Z W : Tensor) (hz : Z.traceFree) (hbz : Z.bianchi)
    (hw : W.traceFree) (hbw : W.bianchi) :
    -(∑ s, t s * rawPairing (rawGradientGenerator s Z.matrix)
      (rawGradientGenerator s W.matrix)) / 40 = diagonalGradientPairing t Z W := by
  have h0 := congrArg (fun x : ℝ => t 0 * x) (generator_row_pairing 0 Z W hz hbz hw hbw)
  have h1 := congrArg (fun x : ℝ => t 1 * x) (generator_row_pairing 1 Z W hz hbz hw hbw)
  have h2 := congrArg (fun x : ℝ => t 2 * x) (generator_row_pairing 2 Z W hz hbz hw hbw)
  have htrace := congrArg (fun x : ℝ => 25 * x * rawPairing Z.matrix W.matrix) ht
  simp only [diagonalGradientPairing, Fin.sum_univ_three] at h0 h1 h2 htrace ⊢
  linear_combination (-1 / 40 : ℝ) * (h0 + h1 + h2 + htrace)

def mixedCouplingPairing (s : Fin 3) (Z W : Tensor) : ℝ :=
  ∑ a, ∑ b, inner ℝ (quaternion s (matrixRotation s Z a b)) (W.matrix a b)

/-- The one-fifth derivative-slot compression also holds in the bilinear form. -/
theorem mixedCouplingPairing_eq (s : Fin 3) (Z W : Tensor)
    (hz : Z.traceFree) (hbz : Z.bianchi) (hbw : W.bianchi) :
    mixedCouplingPairing s Z W = rawPairing Z.matrix W.matrix -
      (1 / 5 : ℝ) * rawPairing (rawGradientGenerator s Z.matrix)
        (rawGradientGenerator s W.matrix) := by
  have hp := derivativeQuaternion_pairing s W (totalGradientTensor s Z) hbw
    (totalGradientTensor_bianchi s Z hz hbz)
  rw [totalGradientTensor_matrix s Z hz hbz] at hp
  rw [rawPairing_comm (rawGradientGenerator s W.matrix),
    rawPairing_vectors] at hp
  simp only [derivativeQuaternion_matrix] at hp
  have hpoint (a b : Fin 3) :
      inner ℝ (quaternion s (matrixRotation s Z a b)) (W.matrix a b) =
        inner ℝ (Z.matrix a b) (W.matrix a b) -
          inner ℝ (quaternion s (W.matrix a b)) (rawGradientGenerator s Z.matrix a b) := by
    rw [quaternion_inner_skew, rawGradientGenerator_matrix, gradientGenerator,
      inner_add_right, quaternion_inner]
    rw [real_inner_comm (matrixRotation s Z a b),
      real_inner_comm (W.matrix a b)]
    ring
  simp_rw [mixedCouplingPairing, hpoint, Finset.sum_sub_distrib]
  rw [← rawPairing_vectors, hp]

/-- Exact mixed compression, with arbitrary actual Bianchi tensors in both slots. -/
theorem weighted_mixedCouplingPairing (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (Z W : Tensor) (hz : Z.traceFree) (hbz : Z.bianchi)
    (hw : W.traceFree) (hbw : W.bianchi) :
    (∑ s, t s * mixedCouplingPairing s Z W) = 8 * diagonalGradientPairing t Z W := by
  have he := weighted_generator_pairing t ht Z W hz hbz hw hbw
  calc
    _ = (∑ s, t s) * rawPairing Z.matrix W.matrix - (1 / 5 : ℝ) *
        (∑ s, t s * rawPairing (rawGradientGenerator s Z.matrix)
          (rawGradientGenerator s W.matrix)) := by
      simp_rw [mixedCouplingPairing_eq _ Z W hz hbz hbw]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by
      rw [ht, zero_mul]
      linarith

/-- The actual trace-free anticommutator, applied independently in each
derivative direction. -/
def rawMatrixCurvature (t : Fin 3 → ℝ) (Z : Tensor) : RawGradient := fun a b =>
  ((t a + t b) / 2) • Z.matrix a b -
    if a = b then (1 / 3 : ℝ) • (∑ c, t c • Z.diagonal c) else 0

theorem rawMatrixCurvature_component (t : Fin 3 → ℝ) (Z : Tensor)
    (a b : Fin 3) (j : Fin 4) :
    rawMatrixCurvature t Z a b j =
      diagonalCurvatureAction t (fun a b => Z.matrix a b j) a b := by
  have hdiag (c : Fin 3) : Z.diagonal c = Z.matrix c c := by
    fin_cases c <;> rfl
  simp only [rawMatrixCurvature, diagonalCurvatureAction, hdiag]
  split_ifs
  all_goals simp [WithLp.ofLp_sum, Finset.sum_apply]
  all_goals ring

theorem rawMatrixCurvature_shape (S : Shape) (v : ℝ) (Z : Tensor) :
    rawMatrixCurvature (fun s => v * S.s s) Z = (matrixCurvatureTensor S v Z).matrix := by
  funext a b
  ext j
  rw [rawMatrixCurvature_component, matrixCurvatureTensor_matrix]

/-- The trace correction is orthogonal to the trace-free second argument. -/
theorem rawMatrixCurvature_pairing (t : Fin 3 → ℝ) (Z W : Tensor)
    (hw : W.traceFree) :
    rawPairing (rawMatrixCurvature t Z) W.matrix = diagonalGradientPairing t Z W := by
  let C : Vec := ∑ c, t c • Z.diagonal c
  have htrace : (∑ a, inner ℝ C (W.matrix a a)) = 0 := by
    have hd (a : Fin 3) : W.matrix a a = W.diagonal a := by fin_cases a <;> rfl
    simp_rw [hd]
    rw [← inner_sum, hw, inner_zero_right]
  have hcolumn : (∑ a, ∑ b, t b * inner ℝ (Z.matrix a b) (W.matrix a b)) =
      ∑ a, ∑ b, t a * inner ℝ (Z.matrix a b) (W.matrix a b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Z.matrix_symmetric b a, W.matrix_symmetric b a]
  have hpoint (a b : Fin 3) :
      inner ℝ (rawMatrixCurvature t Z a b) (W.matrix a b) =
        (t a * inner ℝ (Z.matrix a b) (W.matrix a b) +
          t b * inner ℝ (Z.matrix a b) (W.matrix a b)) / 2 -
            if a = b then (1 / 3 : ℝ) * inner ℝ C (W.matrix a a) else 0 := by
    by_cases hab : a = b
    · subst b
      simp only [rawMatrixCurvature, ite_true, inner_sub_left, real_inner_smul_left]
      ring
    · simp only [rawMatrixCurvature, hab, ite_false, sub_zero, real_inner_smul_left]
      ring
  rw [rawPairing_vectors]
  simp only [hpoint, Finset.sum_sub_distrib]
  simp only [← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hcorrection : (∑ a, (1 / 3 : ℝ) * inner ℝ C (W.matrix a a)) = 0 := by
    rw [← Finset.mul_sum, htrace, mul_zero]
  rw [hcorrection, hcolumn]
  simp only [diagonalGradientPairing, Finset.mul_sum]
  ring

/-- The requested arbitrary-argument compression in actual matrix entries. -/
theorem weighted_mixed_rawMatrixCurvature (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (Z W : Tensor) (hz : Z.traceFree) (hbz : Z.bianchi)
    (hw : W.traceFree) (hbw : W.bianchi) :
    (∑ s, t s * mixedCouplingPairing s Z W) =
      8 * rawPairing (rawMatrixCurvature t Z) W.matrix := by
  rw [rawMatrixCurvature_pairing t Z W hw]
  exact weighted_mixedCouplingPairing t ht Z W hz hbz hw hbw

/-- The row pairing is the actual matrix-slot curvature operator, with its
normalization inherited from the Frobenius tensor pairing. -/
theorem diagonalGradientPairing_curvatureBilinear (S : Shape) (v : ℝ) (Z W : Tensor) :
    diagonalGradientPairing (fun s => v * S.s s) Z W =
      6 * curvatureBilinear S v Z W := by
  have hs := S.trace_coordinates
  simp [diagonalGradientPairing, curvatureBilinear, Tensor.matrix,
    Fin.sum_univ_three, hs]
  ring

/-- The weighted mixed operator agrees with eight times the actual
uncompressed matrix-slot operator, against every Bianchi test tensor. -/
theorem weighted_mixed_matrixCurvature (S : Shape) (v : ℝ) (Z W : Tensor)
    (hz : Z.traceFree) (hbz : Z.bianchi) (hw : W.traceFree) (hbw : W.bianchi) :
    (∑ s, (v * S.s s) * mixedCouplingPairing s Z W) =
      8 * rawPairing (matrixCurvatureTensor S v Z).matrix W.matrix := by
  have ht : ∑ s, v * S.s s = 0 := by
    rw [← Finset.mul_sum, S.trace, mul_zero]
  rw [weighted_mixedCouplingPairing _ ht Z W hz hbz hw hbw,
    diagonalGradientPairing_curvatureBilinear, tensor_pairing_eq_raw,
    matrixCurvatureTensor_pairing S v Z W hw]

/-- After orthogonal Bianchi compression the same bilinear identity pairs
with the concrete transported operator, including when the test tensor is
that operator itself. -/
theorem weighted_mixed_curvatureAction (S : Shape) (v : ℝ) (p k l : Vec)
    (W : Tensor) (hw : W.traceFree) (hbw : W.bianchi) :
    (∑ s, (v * S.s s) * mixedCouplingPairing s (parameters S p k l) W) =
      48 * (curvatureAction S v p k l).pairing W := by
  rw [weighted_mixed_matrixCurvature S v _ W (parameters_traceFree S p k l)
    (parameters_bianchi S p k l) hw hbw, tensor_pairing_eq_raw,
    ← curvatureAction_compression S v p k l W hw hbw]
  ring

/-- Testing with the compressed curvature action gives its exact squared
energy, the term used in the nonparallel matrix-slot Green identity. -/
theorem weighted_mixed_curvatureAction_energy (S : Shape) (v : ℝ) (p k l : Vec) :
    (∑ s, (v * S.s s) * mixedCouplingPairing s (parameters S p k l)
      (curvatureAction S v p k l)) =
        8 * (curvatureAction S v p k l).squaredNorm := by
  have ht : (curvatureAction S v p k l).traceFree := parameters_traceFree S _ _ _
  have hb : (curvatureAction S v p k l).bianchi := parameters_bianchi S _ _ _
  rw [weighted_mixed_curvatureAction S v p k l (curvatureAction S v p k l) ht hb]
  simp only [Tensor.pairing, Tensor.squaredNorm, real_inner_self_eq_norm_sq]
  ring

end
end PositiveEinsteinFour.Bianchi

end OAI
