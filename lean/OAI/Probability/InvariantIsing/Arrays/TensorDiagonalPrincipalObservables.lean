import OAI.Probability.InvariantIsing.Arrays.TensorPrincipalBlock

namespace OAI

/-! The one- and two-replica principal observables for the diagonal Ward
identity, with a generic spin projection for countable leaf passage. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*}

def tensorDiagonalDirect {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 1 → X) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0)) j ^ 2 -
      spinCoordinate (specialToOrthogonal U) (sp (σ 0)) i ^ 2 +
      coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) *
        ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal U) (sp (σ 0))))

def tensorDiagonalFresh {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 2 → X) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
    coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) *
      ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal U) (sp (σ 1)))

def tensorDiagonalDirectCap {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, ((N : ℝ) + N * (|eig i - eig j| * N))

def tensorDiagonalFreshCap {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, (N : ℝ) * (|eig i - eig j| * N)

lemma tensorDiagonalDirectCap_nonneg {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) :
    0 ≤ tensorDiagonalDirectCap eig J K := by
  unfold tensorDiagonalDirectCap
  positivity

lemma tensorDiagonalFreshCap_nonneg {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) :
    0 ≤ tensorDiagonalFreshCap eig J K := by
  unfold tensorDiagonalFreshCap
  positivity

lemma tensorDiagonalDirect_abs_le {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 1 → X) :
    |tensorDiagonalDirect eig J K sp U σ| ≤ tensorDiagonalDirectCap eig J K := by
  unfold tensorDiagonalDirect tensorDiagonalDirectCap
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (abs_add_le _ _).trans
  apply add_le_add (abs_coordinateSquareDifference_le i j _ _)
  rw [abs_mul, abs_mul]
  exact mul_le_mul (abs_coordinateProduct_le i j _ _)
    (mul_le_mul_of_nonneg_left (abs_coordinateProduct_le i j _ _) (abs_nonneg _))
    (by positivity) (Nat.cast_nonneg _)

lemma tensorDiagonalFresh_abs_le {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 2 → X) :
    |tensorDiagonalFresh eig J K sp U σ| ≤ tensorDiagonalFreshCap eig J K := by
  unfold tensorDiagonalFresh tensorDiagonalFreshCap
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul, abs_mul]
  exact mul_le_mul (abs_coordinateProduct_le i j _ _)
    (mul_le_mul_of_nonneg_left (abs_coordinateProduct_le i j _ _) (abs_nonneg _))
    (by positivity) (Nat.cast_nonneg _)

lemma measurable_tensorDiagonalDirect_at {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (σ : Fin 1 → X) :
    Measurable (fun U => tensorDiagonalDirect eig J K sp U σ) := by
  unfold tensorDiagonalDirect coordinateProduct
  have hc (s : X) (a : Fin N) :=
    (measurable_spinCoordinate (sp s) a).comp measurable_specialToOrthogonal
  exact (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (((hc (σ 0) j).pow_const 2).sub ((hc (σ 0) i).pow_const 2)).add
      (((hc (σ 0) i).mul (hc (σ 0) j)).mul
        (((hc (σ 0) i).mul (hc (σ 0) j)).const_mul _))).const_mul _

lemma measurable_tensorDiagonalFresh_at {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (σ : Fin 2 → X) :
    Measurable (fun U => tensorDiagonalFresh eig J K sp U σ) := by
  unfold tensorDiagonalFresh coordinateProduct
  have hc (s : X) (a : Fin N) :=
    (measurable_spinCoordinate (sp s) a).comp measurable_specialToOrthogonal
  exact (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (((hc (σ 0) i).mul (hc (σ 0) j)).mul
      (((hc (σ 1) i).mul (hc (σ 1) j)).const_mul _))).const_mul _

lemma measurable_tensorDiagonalDirect [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (sp : X → Spin N) :
    Measurable (Function.uncurry (tensorDiagonalDirect eig J K sp)) :=
  measurable_from_prod_countable_left (fun σ => measurable_tensorDiagonalDirect_at eig J K sp σ)

lemma measurable_tensorDiagonalFresh [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (sp : X → Spin N) :
    Measurable (Function.uncurry (tensorDiagonalFresh eig J K sp)) :=
  measurable_from_prod_countable_left (fun σ => measurable_tensorDiagonalFresh_at eig J K sp σ)

def tensorDiagonalBlockDirect {N : ℕ} (J K : Finset (Fin N)) (δ : ℝ)
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 1 → X) : ℝ :=
  let A := fun L => projectedOverlap (specialRotation U) L (sp (σ 0)) (sp (σ 0))
  ((J.card : ℝ) / N) * A K - ((K.card : ℝ) / N) * A J + δ * A J * A K

def tensorDiagonalBlockFresh {N : ℕ} (J K : Finset (Fin N)) (δ : ℝ)
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 2 → X) : ℝ :=
  δ * projectedOverlap (specialRotation U) J (sp (σ 0)) (sp (σ 1)) *
    projectedOverlap (specialRotation U) K (sp (σ 0)) (sp (σ 1))

lemma tensorDiagonalDirect_eq_block {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (a b : ℝ)
    (hJ : ∀ i ∈ J, eig i = a) (hK : ∀ j ∈ K, eig j = b)
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 1 → X) :
    tensorDiagonalDirect eig J K sp U σ = tensorDiagonalBlockDirect J K (a-b) sp U σ := by
  unfold tensorDiagonalDirect
  have he : (∑ i ∈ J, ∑ j ∈ K,
      (spinCoordinate (specialToOrthogonal U) (sp (σ 0)) j ^ 2 -
        spinCoordinate (specialToOrthogonal U) (sp (σ 0)) i ^ 2 +
        coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) *
          ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal U) (sp (σ 0))))) =
      ∑ i ∈ J, ∑ j ∈ K,
        (spinCoordinate (specialToOrthogonal U) (sp (σ 0)) j ^ 2 -
          spinCoordinate (specialToOrthogonal U) (sp (σ 0)) i ^ 2 +
          (a-b) * (coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) *
            coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)))) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hJ i hi, hK j hj]
    ring
  rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, coordinateProduct, pow_two]
  have hd := off_coordinate_difference_sum J K
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0)))
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0))) 1
  simp only [mul_one] at hd
  have hp := off_coordinate_fresh_sum J K
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0)))
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0)))
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0))) 1
  simp only [mul_one] at hp
  rw [hd, hp]
  simp only [tensorDiagonalBlockDirect, ← matrixRotation_specialToOrthogonal, projectedOverlap,
    spinCoordinate, div_eq_mul_inv]
  ring

lemma tensorDiagonalFresh_eq_block {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (a b : ℝ)
    (hJ : ∀ i ∈ J, eig i = a) (hK : ∀ j ∈ K, eig j = b)
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 2 → X) :
    tensorDiagonalFresh eig J K sp U σ = tensorDiagonalBlockFresh J K (a-b) sp U σ := by
  unfold tensorDiagonalFresh
  have he : (∑ i ∈ J, ∑ j ∈ K,
      coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) *
        ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal U) (sp (σ 1)))) =
      ∑ i ∈ J, ∑ j ∈ K, (a-b) *
        (coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) *
          coordinateProduct i j (specialToOrthogonal U) (sp (σ 1))) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hJ i hi, hK j hj]
    ring
  rw [he]
  simp only [← Finset.mul_sum, coordinateProduct]
  have hp := off_coordinate_fresh_sum J K
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0)))
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0)))
    (spinCoordinate (specialToOrthogonal U) (sp (σ 1))) 1
  simp only [mul_one] at hp
  rw [hp]
  simp only [tensorDiagonalBlockFresh, ← matrixRotation_specialToOrthogonal, projectedOverlap,
    spinCoordinate]
  ring

end InvariantIsing

end

end OAI
