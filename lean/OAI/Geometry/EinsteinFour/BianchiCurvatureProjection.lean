import OAI.Geometry.EinsteinFour.BianchiHessian
import OAI.Geometry.EinsteinFour.GradientPairing

namespace OAI

/-! The actual matrix-slot curvature form and its Bianchi compression. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- The uncompressed matrix-slot operator, specialized to the diagonal
curvature block `v * S.s`. -/
def matrixCurvatureTensor (S : Shape) (v : ℝ) (Z : Tensor) : Tensor where
  diagonal a := v • (S.s a • Z.diagonal a -
    (1 / 3 : ℝ) • (∑ c, S.s c • Z.diagonal c))
  off a := (-(v * S.s a) / 2) • Z.off a

/-- The trace-free anticommutator lands in the actual trace-free matrix space. -/
theorem matrixCurvatureTensor_traceFree (S : Shape) (v : ℝ) (Z : Tensor) :
    (matrixCurvatureTensor S v Z).traceFree := by
  simp only [Tensor.traceFree, matrixCurvatureTensor, Fin.sum_univ_three]
  module

/-- The coordinate pairing used for the raw commutator has the expected
normalization relative to the Bianchi energy metric. -/
theorem tensor_pairing_eq_raw (Z W : Tensor) :
    rawPairing Z.matrix W.matrix = 6 * Z.pairing W := by
  rw [rawPairing_vectors]
  unfold Tensor.pairing
  ring

/-- The symmetric bilinear version of the actual matrix contraction. -/
def curvatureBilinear (S : Shape) (v : ℝ) (Z W : Tensor) : ℝ :=
  (v / 6) * ((∑ a, S.s a * inner ℝ (Z.diagonal a) (W.diagonal a)) -
    ∑ a, S.s a * inner ℝ (Z.off a) (W.off a))

/-- Matrix entries agree with the invariant trace-free anticommutator. -/
theorem matrixCurvatureTensor_matrix (S : Shape) (v : ℝ) (Z : Tensor)
    (a b : Fin 3) (j : Fin 4) :
    (matrixCurvatureTensor S v Z).matrix a b j =
      diagonalCurvatureAction (fun s => v * S.s s)
        (fun a b => Z.matrix a b j) a b := by
  have hs := S.trace_coordinates
  fin_cases a <;> fin_cases b <;>
    simp [matrixCurvatureTensor, diagonalCurvatureAction, Tensor.matrix,
      Fin.sum_univ_three, hs]
  all_goals first | (left; ring) | ring

/-- The trace correction vanishes when paired with a trace-free tensor. -/
theorem matrixCurvatureTensor_pairing (S : Shape) (v : ℝ) (Z W : Tensor)
    (hw : W.traceFree) :
    (matrixCurvatureTensor S v Z).pairing W = curvatureBilinear S v Z W := by
  have hzero : inner ℝ (∑ c, S.s c • Z.diagonal c) (∑ a, W.diagonal a) = 0 := by
    rw [hw, inner_zero_right]
  simp only [Fin.sum_univ_three, inner_add_right, inner_add_left,
    real_inner_smul_left] at hzero
  simp [Tensor.pairing, Tensor.matrix, matrixCurvatureTensor,
    curvatureBilinear, Fin.sum_univ_three, inner_sub_left,
    real_inner_smul_left]
  simp only [inner_add_left, real_inner_smul_left]
  linear_combination (-v / 18) * hzero

private theorem parameters_add_diagonal (S : Shape) (p k l p' k' l' : Vec)
    (a : Fin 3) :
    (parameters S (p + p') (k + k') (l + l')).diagonal a =
      (parameters S p k l).diagonal a + (parameters S p' k' l').diagonal a := by
  simp only [parameters, smul_add]
  module

private theorem parameters_add_off (S : Shape) (p k l p' k' l' : Vec)
    (a : Fin 3) :
    (parameters S (p + p') (k + k') (l + l')).off a =
      (parameters S p k l).off a + (parameters S p' k' l').off a := by
  simp only [parameters, smul_add, quaternion_add]
  module

/-- Polarization identifies the full operator, not only its quadratic form. -/
theorem curvatureAction_bilinear (S : Shape) (v : ℝ) (p k l p' k' l' : Vec) :
    (curvatureAction S v p k l).pairing (parameters S p' k' l') =
      curvatureBilinear S v (parameters S p k l) (parameters S p' k' l') := by
  have hpol : curvatureContraction S v (parameters S (p + p') (k + k') (l + l')) =
      curvatureContraction S v (parameters S p k l) +
        2 * curvatureBilinear S v (parameters S p k l) (parameters S p' k' l') +
          curvatureContraction S v (parameters S p' k' l') := by
    unfold curvatureContraction curvatureBilinear
    simp_rw [parameters_add_diagonal, parameters_add_off, norm_add_sq_real]
    simp only [Finset.sum_add_distrib, mul_add, Fin.sum_univ_three]
    ring
  rw [curvatureContraction_parameters, curvatureContraction_parameters,
    curvatureContraction_parameters] at hpol
  simp only [norm_add_sq_real, inner_add_left, inner_add_right,
    real_inner_comm] at hpol
  rw [curvatureAction_pairing]
  have hr := S.rho_div_sqrt_three
  rw [show 8 * S.rho / Real.sqrt 3 = 8 * S.skewMoment by
    rw [mul_div_assoc, hr]] at hpol
  linear_combination (1 / 2 : ℝ) * hpol

/-- The transported operator represents matrix-slot curvature against every
actual Bianchi gradient. This is the defining orthogonal compression property. -/
theorem curvatureAction_compression (S : Shape) (v : ℝ) (p k l : Vec)
    (W : Tensor) (hw : W.traceFree) (hb : W.bianchi) :
    (curvatureAction S v p k l).pairing W =
      (matrixCurvatureTensor S v (parameters S p k l)).pairing W := by
  rw [matrixCurvatureTensor_pairing S v _ W hw]
  rw [← parameters_reconstruction S W hw hb]
  exact curvatureAction_bilinear S v p k l _ _ _

/-- The square of the compressed operator is its pairing with the actual
uncompressed matrix action, so the energy formula is the required `E_B`. -/
theorem curvatureAction_compressed_energy (S : Shape) (v : ℝ) (p k l : Vec) :
    (matrixCurvatureTensor S v (parameters S p k l)).pairing
        (curvatureAction S v p k l) =
      (curvatureAction S v p k l).squaredNorm / 6 := by
  have h := curvatureAction_compression S v p k l (curvatureAction S v p k l)
    (parameters_traceFree S _ _ _) (parameters_bianchi S _ _ _)
  rw [← h]
  simp only [Tensor.pairing, Tensor.squaredNorm, real_inner_self_eq_norm_sq]

end
end PositiveEinsteinFour.Bianchi

end OAI
