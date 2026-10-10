import OAI.Geometry.EinsteinFour.TraceHessian

namespace OAI

/-! The actual Bianchi coupling operator on first derivatives. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- Matrix-slot rotation, retaining the actual tangent four-vectors. -/
def matrixRotation (s : Fin 3) (Z : Tensor) (a b : Fin 3) : Vec :=
  (∑ c, rotation s a c • Z.matrix c b) -
    ∑ c, rotation s c b • Z.matrix a c

/-- The coupling in the Bianchi projector `(6-C)/10`. -/
def gradientCoupling (Z : Tensor) (a b : Fin 3) : Vec :=
  ∑ s, quaternion s (matrixRotation s Z a b)

private theorem diagonal_zero_from_bianchi (Z : Tensor) (hb : Z.bianchi) :
    Z.diagonal 0 = Z.auxiliary 2 - Z.auxiliary 1 := by
  apply eq_sub_iff_add_eq.mpr
  apply sub_eq_zero.mp
  simpa [next, previous] using (Z.bianchi_iff.mp hb) 0

private theorem diagonal_one_from_bianchi (Z : Tensor) (hb : Z.bianchi) :
    Z.diagonal 1 = Z.auxiliary 0 - Z.auxiliary 2 := by
  apply eq_sub_iff_add_eq.mpr
  apply sub_eq_zero.mp
  simpa [next, previous] using (Z.bianchi_iff.mp hb) 1

private theorem diagonal_two_from_bianchi (Z : Tensor) (hb : Z.bianchi) :
    Z.diagonal 2 = Z.auxiliary 1 - Z.auxiliary 0 := by
  apply eq_sub_iff_add_eq.mpr
  apply sub_eq_zero.mp
  simpa [next, previous] using (Z.bianchi_iff.mp hb) 2

private theorem gradientCoupling_zero (Z : Tensor) (hb : Z.bianchi) (b : Fin 3) :
    gradientCoupling Z 0 b = (-4 : ℝ) • Z.matrix 0 b := by
  have h0 := diagonal_zero_from_bianchi Z hb
  have h1 := diagonal_one_from_bianchi Z hb
  have h2 := diagonal_two_from_bianchi Z hb
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [gradientCoupling, matrixRotation, rotation, Tensor.matrix,
      Fin.sum_univ_succ, h0, h1, h2, Tensor.auxiliary, quaternion]
  all_goals ring

private theorem gradientCoupling_one (Z : Tensor) (hb : Z.bianchi) (b : Fin 3) :
    gradientCoupling Z 1 b = (-4 : ℝ) • Z.matrix 1 b := by
  have h0 := diagonal_zero_from_bianchi Z hb
  have h1 := diagonal_one_from_bianchi Z hb
  have h2 := diagonal_two_from_bianchi Z hb
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [gradientCoupling, matrixRotation, rotation, Tensor.matrix,
      Fin.sum_univ_succ, h0, h1, h2, Tensor.auxiliary, quaternion]
  all_goals ring

private theorem gradientCoupling_two (Z : Tensor) (hb : Z.bianchi) (b : Fin 3) :
    gradientCoupling Z 2 b = (-4 : ℝ) • Z.matrix 2 b := by
  have h0 := diagonal_zero_from_bianchi Z hb
  have h1 := diagonal_one_from_bianchi Z hb
  have h2 := diagonal_two_from_bianchi Z hb
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [gradientCoupling, matrixRotation, rotation, Tensor.matrix,
      Fin.sum_univ_succ, h0, h1, h2, Tensor.auxiliary, quaternion]
  all_goals ring

/-- The Bianchi equation puts every gradient in the actual `C=-4` subspace. -/
theorem gradientCoupling_eq (Z : Tensor) (hb : Z.bianchi) (a b : Fin 3) :
    gradientCoupling Z a b = (-4 : ℝ) • Z.matrix a b := by
  fin_cases a
  · exact gradientCoupling_zero Z hb b
  · exact gradientCoupling_one Z hb b
  · exact gradientCoupling_two Z hb b

/-- Quaternion multiplication preserves the full Euclidean inner product. -/
theorem quaternion_inner (s : Fin 3) (p q : Vec) :
    inner ℝ (quaternion s p) (quaternion s q) = inner ℝ p q := by
  have h := quaternion_norm_sq s (p + q)
  rw [quaternion_add, norm_add_sq_real, norm_add_sq_real,
    quaternion_norm_sq, quaternion_norm_sq] at h
  linarith

/-- The infinitesimal quaternion action is skew-adjoint. -/
theorem quaternion_inner_skew (s : Fin 3) (p q : Vec) :
    inner ℝ (quaternion s p) q = -inner ℝ p (quaternion s q) := by
  have h := quaternion_inner s p (quaternion s q)
  rw [quaternion_square, inner_neg_right] at h
  linarith

private theorem rotate_sums (f : Fin 3 → Fin 3 → Fin 3 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ s, ∑ u, f a b s u) = ∑ u, ∑ a, ∑ b, ∑ s, f a b s u := by
  calc
    _ = ∑ a, ∑ b, ∑ u, ∑ s, f a b s u := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ u, ∑ b, ∑ s, f a b s u := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

private theorem matrixRotation_component (s : Fin 3) (Z : Tensor)
    (a b : Fin 3) (u : Fin 4) :
    matrixRotation s Z a b u = matrixAction s (fun a b => Z.matrix a b u) a b := by
  simp [matrixRotation, matrixAction, Finset.sum_sub_distrib,
    Fin.sum_univ_succ]
  ring

/-- The matrix-spin Casimir on the actual four-vector-valued tensor. -/
theorem matrixRotation_energy (Z : Tensor) (hz : Z.traceFree) :
    (∑ a, ∑ b, ∑ s, ‖matrixRotation s Z a b‖ ^ 2) = 24 * Z.squaredNorm := by
  let M (u : Fin 4) : Mat := fun a b => Z.matrix a b u
  have hs (u : Fin 4) : symmetric (M u) := by
    intro a b
    exact congrArg (fun q : Vec => q u) (Z.matrix_symmetric a b)
  have ht (u : Fin 4) : traceFree (M u) := by
    have h := congrArg (fun q : Vec => q u) hz
    simpa [traceFree, M, Tensor.traceFree, Tensor.matrix, Fin.sum_univ_succ] using h
  have hc (u : Fin 4) := matrixAction_casimir (M u) (hs u) (ht u)
  have hr : (∑ u : Fin 4, ∑ a, ∑ b, Z.matrix a b u ^ 2) = Z.squaredNorm := by
    unfold Tensor.squaredNorm
    simp only [EuclideanSpace.real_norm_sq_eq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [rotate_sums]
  simp_rw [matrixRotation_component]
  change (∑ u : Fin 4, ∑ a, ∑ b, ∑ s, matrixAction s (M u) a b ^ 2) = _
  simp_rw [hc]
  simp only [matrixNormSq, M, ← Finset.mul_sum]
  rw [hr]

/-- The actual total plus generator on a Bianchi gradient. -/
def gradientGenerator (s : Fin 3) (Z : Tensor) (a b : Fin 3) : Vec :=
  quaternion s (Z.matrix a b) + matrixRotation s Z a b

/-- The Bianchi gradient has the exact inner Casimir energy 35. -/
theorem gradientGenerator_energy (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ a, ∑ b, ∑ s, ‖gradientGenerator s Z a b‖ ^ 2) = 35 * Z.squaredNorm := by
  have hi : (∑ a, ∑ b, ∑ s : Fin 3, ‖quaternion s (Z.matrix a b)‖ ^ 2) =
      3 * Z.squaredNorm := by
    simp [Tensor.squaredNorm, Fin.sum_univ_succ]
    ring
  have he (a b : Fin 3) :
      (∑ s, inner ℝ (quaternion s (Z.matrix a b)) (matrixRotation s Z a b)) =
        4 * ‖Z.matrix a b‖ ^ 2 := by
    simp only [quaternion_inner_skew, Finset.sum_neg_distrib]
    rw [← inner_sum]
    change -inner ℝ (Z.matrix a b) (gradientCoupling Z a b) = _
    rw [gradientCoupling_eq Z hb]
    simp [real_inner_smul_right]
  have hx : (∑ a, ∑ b, ∑ s,
      inner ℝ (quaternion s (Z.matrix a b)) (matrixRotation s Z a b)) =
      4 * Z.squaredNorm := by
    simp_rw [he]
    simp only [← Finset.mul_sum, Tensor.squaredNorm]
  have hr := matrixRotation_energy Z hz
  have hsplit : (∑ a, ∑ b, ∑ s, ‖gradientGenerator s Z a b‖ ^ 2) =
      (∑ a, ∑ b, ∑ s : Fin 3, ‖quaternion s (Z.matrix a b)‖ ^ 2) +
      (∑ a, ∑ b, ∑ s, ‖matrixRotation s Z a b‖ ^ 2) +
      2 * (∑ a, ∑ b, ∑ s,
        inner ℝ (quaternion s (Z.matrix a b)) (matrixRotation s Z a b)) := by
    simp only [gradientGenerator, norm_add_sq_real, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    ring
  rw [hsplit, hi, hr, hx]
  ring

end
end PositiveEinsteinFour.Bianchi

end OAI
