import OAI.Geometry.EinsteinFour.GradientPairing
import OAI.Geometry.EinsteinFour.GradientCoordinates

namespace OAI

/-! The scalar contraction of the commuted Weyl equation. The compression
coefficient is derived on the actual Bianchi tensor, not taken from a
representation label or assumed as the manuscript's differential equation. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

def totalGradientTensor (s : Fin 3) (Z : Tensor) : Tensor where
  diagonal a := rawGradientGenerator s Z.matrix a a
  off a := rawGradientGenerator s Z.matrix (next a) (previous a)

private theorem totalGradientTensor_coordinates (s : Fin 3) (v : Fin 3 → Vec) :
    totalGradientTensor s (costParameters v) = costParameters (generatorCoordinates s v) := by
  apply Tensor.ext
  · funext a
    change rawGradientGenerator s (costParameters v).matrix a a = _
    rw [generator_coordinates]
    fin_cases a <;> rfl
  · funext a
    change rawGradientGenerator s (costParameters v).matrix (next a) (previous a) = _
    rw [generator_coordinates]
    fin_cases a <;> rfl

theorem totalGradientTensor_matrix (s : Fin 3) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (totalGradientTensor s Z).matrix = rawGradientGenerator s Z.matrix := by
  obtain ⟨v, rfl⟩ := exists_costParameters Z hz hb
  rw [totalGradientTensor_coordinates, generator_coordinates]

theorem totalGradientTensor_bianchi (s : Fin 3) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) : (totalGradientTensor s Z).bianchi := by
  obtain ⟨v, rfl⟩ := exists_costParameters Z hz hb
  rw [totalGradientTensor_coordinates]
  exact parameters_bianchi _ _ _ _

def mixedCouplingForm (s : Fin 3) (Z : Tensor) : ℝ :=
  ∑ a, ∑ b, inner ℝ (quaternion s (matrixRotation s Z a b)) (Z.matrix a b)

def diagonalGradientForm (t : Fin 3 → ℝ) (Z : Tensor) : ℝ :=
  ∑ s, t s * (∑ b, ‖Z.matrix s b‖ ^ 2)

/-- The single-generator compression follows from the actual Bianchi
projector and the preserved gradient tensor. -/
theorem mixedCouplingForm_eq (s : Fin 3) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    mixedCouplingForm s Z = Z.squaredNorm -
      (1 / 5 : ℝ) * (∑ a, ∑ b, ‖rawGradientGenerator s Z.matrix a b‖ ^ 2) := by
  have hp := derivativeQuaternion_pairing s Z (totalGradientTensor s Z) hb
    (totalGradientTensor_bianchi s Z hz hb)
  rw [rawPairing_vectors, rawPairing_vectors, totalGradientTensor_matrix s Z hz hb] at hp
  simp only [derivativeQuaternion_matrix, real_inner_self_eq_norm_sq] at hp
  have hpoint (a b : Fin 3) :
      inner ℝ (quaternion s (matrixRotation s Z a b)) (Z.matrix a b) =
        ‖Z.matrix a b‖ ^ 2 -
          inner ℝ (quaternion s (Z.matrix a b)) (rawGradientGenerator s Z.matrix a b) := by
    rw [quaternion_inner_skew,
      real_inner_comm (quaternion s (Z.matrix a b)) (matrixRotation s Z a b),
      rawGradientGenerator_matrix, gradientGenerator, inner_add_right,
      real_inner_self_eq_norm_sq, quaternion_norm_sq]
    ring
  simp_rw [mixedCouplingForm, hpoint, Finset.sum_sub_distrib]
  change Z.squaredNorm - _ = _
  rw [hp]

/-- Exact weighted mixed compression with no spectral-theory premise. -/
theorem weighted_mixedCouplingForm (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s, t s * mixedCouplingForm s Z) = 8 * diagonalGradientForm t Z := by
  have he := weighted_generator_matrixForm t ht Z hz hb
  calc
    _ = ∑ s, (t s * Z.squaredNorm - (1 / 5 : ℝ) *
        (t s * (∑ a, ∑ b, ‖rawGradientGenerator s Z.matrix a b‖ ^ 2))) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [mixedCouplingForm_eq s Z hz hb]
      ring
    _ = (∑ s, t s) * Z.squaredNorm - (1 / 5 : ℝ) *
        (∑ s, t s * (∑ a, ∑ b, ‖rawGradientGenerator s Z.matrix a b‖ ^ 2)) := by
      simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    _ = _ := by
      rw [ht, zero_mul]
      unfold diagonalGradientForm
      linarith

/-- Contract the raw Ricci-commuted equation against the Bianchi gradient.
The four scalar terms are respectively the derivative of the Weyl equation,
Ricci, the constant coupling, and the curvature-dependent coupling. -/
theorem commuted_laplacian_contraction (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) (L : ℝ)
    (hraw : L = 6 * Z.squaredNorm - 12 * diagonalGradientForm t Z +
      3 * Z.squaredNorm + 4 * Z.squaredNorm - ∑ s, t s * mixedCouplingForm s Z) :
    L = 13 * Z.squaredNorm - 20 * diagonalGradientForm t Z := by
  rw [weighted_mixedCouplingForm t ht Z hz hb] at hraw
  linarith

end

end PositiveEinsteinFour.Bianchi

end OAI
