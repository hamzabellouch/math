import OAI.Geometry.EinsteinFour.GradientOperator
import OAI.Geometry.EinsteinFour.GradientProjection
import OAI.Geometry.EinsteinFour.TensorPairing

namespace OAI

/-! Bilinear compression on the actual Bianchi gradient space. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

abbrev GradientIndex := Fin 4 × Fin 3 × Fin 3

def rawCoordinates (Z : RawGradient) (p : GradientIndex) : ℝ := Z p.2.1 p.2.2 p.1

def rawPairing (Z W : RawGradient) : ℝ :=
  ∑ p : GradientIndex, rawCoordinates Z p * rawCoordinates W p

theorem rawPairing_comm (Z W : RawGradient) : rawPairing Z W = rawPairing W Z := by
  simp only [rawPairing, mul_comm]

theorem rawPairing_vectors (Z W : RawGradient) :
    rawPairing Z W = ∑ a, ∑ b, inner ℝ (Z a b) (W a b) := by
  simp only [rawPairing, rawCoordinates, Fintype.sum_prod_type,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  calc
    _ = ∑ a : Fin 3, ∑ j : Fin 4, ∑ b : Fin 3, Z a b j * W a b j :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      simp only [mul_comm]

theorem rawPairing_add_left (Z W U : RawGradient) :
    rawPairing (Z + W) U = rawPairing Z U + rawPairing W U := by
  change (∑ p : GradientIndex,
    (rawCoordinates Z p + rawCoordinates W p) * rawCoordinates U p) = _
  simp only [add_mul, rawPairing, Finset.sum_add_distrib]

theorem rawPairing_add_right (Z W U : RawGradient) :
    rawPairing Z (W + U) = rawPairing Z W + rawPairing Z U := by
  rw [rawPairing_comm Z, rawPairing_add_left, rawPairing_comm W, rawPairing_comm U]

theorem rawPairing_sum_left {ι : Type*} [Fintype ι]
    (f : ι → RawGradient) (W : RawGradient) :
    rawPairing (∑ i, f i) W = ∑ i, rawPairing (f i) W := by
  simp only [rawPairing_vectors, Finset.sum_apply, sum_inner]
  calc
    _ = ∑ a : Fin 3, ∑ i : ι, ∑ b : Fin 3, inner ℝ (f i a b) (W a b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

def rawCoupling (Z : RawGradient) : RawGradient := fun a b =>
  ∑ s : Fin 3, quaternion s (rawMatrixRotation s Z a b)

def gradientCouplingKernel (p q : GradientIndex) : ℝ := ∑ s : Fin 3,
  quaternionMatrix s p.1 q.1 *
    ((if p.2.2 = q.2.2 then rotation s p.2.1 q.2.1 else 0) +
      (if p.2.1 = q.2.1 then rotation s p.2.2 q.2.2 else 0))

theorem gradientCouplingKernel_symmetric (p q : GradientIndex) :
    gradientCouplingKernel p q = gradientCouplingKernel q p := by
  unfold gradientCouplingKernel
  apply Finset.sum_congr rfl
  intro s _
  rw [quaternionMatrix_skew s p.1 q.1,
    rotation_skew s p.2.1 q.2.1, rotation_skew s p.2.2 q.2.2]
  simp only [eq_comm (a := q.2.1) (b := p.2.1),
    eq_comm (a := q.2.2) (b := p.2.2)]
  split_ifs <;> ring

theorem rawCoupling_coordinates (Z : RawGradient) (p : GradientIndex) :
    rawCoordinates (rawCoupling Z) p =
      ∑ q : GradientIndex, gradientCouplingKernel p q * rawCoordinates Z q := by
  rcases p with ⟨j, a, b⟩
  simp only [gradientCouplingKernel, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold rawCoupling rawCoordinates
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [← quaternionMatrix_apply]
  simp [Fintype.sum_prod_type, rawMatrixRotation,
    add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    ]
  have hneg (k : Fin 4) :
      (∑ c, quaternionMatrix s j k * rotation s c b * Z a c k) =
        -(∑ c, quaternionMatrix s j k * rotation s b c * Z a c k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [rotation_skew s c b]
    ring
  change (∑ k : Fin 4,
      quaternionMatrix s j k * ((∑ c, rotation s a c * Z c b k) -
        ∑ c, rotation s c b * Z a c k)) =
    (∑ k : Fin 4, ∑ c, quaternionMatrix s j k * rotation s a c * Z c b k) +
      ∑ k : Fin 4, ∑ c, quaternionMatrix s j k * rotation s b c * Z a c k
  calc
    _ = (∑ k : Fin 4, ∑ c, quaternionMatrix s j k * rotation s a c * Z c b k) -
        ∑ k : Fin 4, ∑ c, quaternionMatrix s j k * rotation s c b * Z a c k := by
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, mul_assoc]
    _ = _ := by
      simp only [hneg, Finset.sum_neg_distrib]
      ring

theorem rawCoupling_selfadjoint (Z W : RawGradient) :
    rawPairing (rawCoupling Z) W = rawPairing Z (rawCoupling W) := by
  simp only [rawPairing, rawCoupling_coordinates, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [gradientCouplingKernel_symmetric q p]
  ring

theorem rawCoupling_matrix (Z : Tensor) : rawCoupling Z.matrix = gradientCoupling Z := rfl

theorem rawPairing_smul_left (r : ℝ) (Z W : RawGradient) :
    rawPairing (r • Z) W = r * rawPairing Z W := by
  change (∑ p : GradientIndex, (r * rawCoordinates Z p) * rawCoordinates W p) = _
  simp only [mul_assoc, rawPairing, ← Finset.mul_sum]

theorem rawPairing_smul_right (r : ℝ) (Z W : RawGradient) :
    rawPairing Z (r • W) = r * rawPairing Z W := by
  change (∑ p : GradientIndex, rawCoordinates Z p * (r * rawCoordinates W p)) = _
  simp only [mul_left_comm, rawPairing, ← Finset.mul_sum]

theorem rawPairing_sub_left (Z W U : RawGradient) :
    rawPairing (Z - W) U = rawPairing Z U - rawPairing W U := by
  change (∑ p : GradientIndex,
    (rawCoordinates Z p - rawCoordinates W p) * rawCoordinates U p) = _
  simp only [sub_mul, rawPairing, Finset.sum_sub_distrib]

/-- Pairing with a genuine Bianchi tensor removes the displayed polynomial
projection, by self-adjointness of the actual finite-dimensional coupling. -/
theorem gradientProjection_pairing (Z W : Tensor) (hw : W.bianchi) :
    rawPairing (gradientProjection Z) W.matrix = rawPairing Z.matrix W.matrix := by
  have hW : rawCoupling W.matrix = (-4 : ℝ) • W.matrix := by
    funext a b
    exact gradientCoupling_eq W hw a b
  have hC := rawCoupling_selfadjoint Z.matrix W.matrix
  rw [hW, rawPairing_smul_right] at hC
  have hP : gradientProjection Z =
      (1 / 10 : ℝ) • ((6 : ℝ) • Z.matrix - rawCoupling Z.matrix) := rfl
  rw [hP, rawPairing_smul_left, rawPairing_sub_left, rawPairing_smul_left, hC]
  ring

/-- The derivative-slot quaternion has the actual one-fifth compression
against any other Bianchi gradient, retaining both bilinear arguments. -/
theorem derivativeQuaternion_pairing (r : Fin 3) (Z W : Tensor)
    (hz : Z.bianchi) (hw : W.bianchi) :
    rawPairing (derivativeQuaternion r Z).matrix W.matrix =
      (1 / 5 : ℝ) * rawPairing (rawGradientGenerator r Z.matrix) W.matrix := by
  have h := gradientProjection_pairing (derivativeQuaternion r Z) W hw
  have hp : gradientProjection (derivativeQuaternion r Z) =
      (1 / 5 : ℝ) • rawGradientGenerator r Z.matrix := by
    funext a b
    exact gradientProjection_derivativeQuaternion r Z hz a b
  rw [hp, rawPairing_smul_left] at h
  exact h.symm

end
end PositiveEinsteinFour.Bianchi

end OAI
