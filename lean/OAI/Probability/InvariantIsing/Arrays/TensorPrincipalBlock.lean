import OAI.Probability.InvariantIsing.Arrays.TensorPrincipalObservables

namespace OAI

/-! The finite principal Ward observables contract exactly to projected
overlap products when the two row groups have constant eigenvalues. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma off_coordinate_difference_sum {N : ℕ} (J K : Finset (Fin N)) (a b : Fin N → ℝ) (F : ℝ) :
    (∑ i ∈ J, ∑ j ∈ K, (a j * b j - a i * b i) * F) =
      ((J.card : ℝ) * (∑ j ∈ K, a j * b j) - (K.card : ℝ) * (∑ i ∈ J, a i * b i)) * F := by
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma off_coordinate_direct_sum {N : ℕ} (J K : Finset (Fin N)) (a b : Fin N → ℝ) (F : ℝ) :
    (∑ i ∈ J, ∑ j ∈ K, a i * b j * F * (a i * a j + b i * b j)) =
      ((∑ i ∈ J, a i * a i) * (∑ j ∈ K, a j * b j) +
        (∑ i ∈ J, a i * b i) * (∑ j ∈ K, b j * b j)) * F := by
  simp only [add_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma off_coordinate_fresh_sum {N : ℕ} (J K : Finset (Fin N)) (a b c : Fin N → ℝ) (F : ℝ) :
    (∑ i ∈ J, ∑ j ∈ K, a i * b j * F * (c i * c j)) =
      (∑ i ∈ J, a i * c i) * (∑ j ∈ K, b j * c j) * F := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {X : Type*}

def tensorOffBlockDirect {N : ℕ} (J K : Finset (Fin N)) (δ : ℝ)
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ) (U : SpecialOrthogonal N) (σ : Fin 2 → X) : ℝ :=
  let A := fun L s t => projectedOverlap (specialRotation U) L (sp s) (sp t)
  F (sp (σ 0)) (sp (σ 1)) *
    (((J.card : ℝ) / N) * A K (σ 0) (σ 1) - ((K.card : ℝ) / N) * A J (σ 0) (σ 1) +
      δ * (A J (σ 0) (σ 0) * A K (σ 0) (σ 1) + A J (σ 0) (σ 1) * A K (σ 1) (σ 1)))

def tensorOffBlockFresh {N : ℕ} (J K : Finset (Fin N)) (δ : ℝ)
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ) (U : SpecialOrthogonal N) (σ : Fin 3 → X) : ℝ :=
  δ * F (sp (σ 0)) (sp (σ 1)) *
    projectedOverlap (specialRotation U) J (sp (σ 0)) (sp (σ 2)) *
    projectedOverlap (specialRotation U) K (sp (σ 1)) (sp (σ 2))

lemma tensorOffDirect_eq_block {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (a b : ℝ)
    (hJ : ∀ i ∈ J, eig i = a) (hK : ∀ j ∈ K, eig j = b)
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ) (U : SpecialOrthogonal N) (σ : Fin 2 → X) :
    tensorOffDirect eig J K sp F U σ = tensorOffBlockDirect J K (a-b) sp F U σ := by
  unfold tensorOffDirect
  have he : (∑ i ∈ J, ∑ j ∈ K,
      (offCoordinateVariation i j F (specialToOrthogonal U) (sp (σ 0), sp (σ 1)) +
        offCoordinateProduct i j F (specialToOrthogonal U) (sp (σ 0), sp (σ 1)) *
          ((eig i - eig j) * (coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) +
            coordinateProduct i j (specialToOrthogonal U) (sp (σ 1)))))) =
      ∑ i ∈ J, ∑ j ∈ K,
        (offCoordinateVariation i j F (specialToOrthogonal U) (sp (σ 0), sp (σ 1)) +
          (a-b) * (offCoordinateProduct i j F (specialToOrthogonal U) (sp (σ 0), sp (σ 1)) *
            (coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) +
              coordinateProduct i j (specialToOrthogonal U) (sp (σ 1))))) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hJ i hi, hK j hj]
    ring
  rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, offCoordinateVariation,
    offCoordinateProduct, coordinateProduct]
  rw [off_coordinate_difference_sum, off_coordinate_direct_sum]
  simp only [tensorOffBlockDirect, ← matrixRotation_specialToOrthogonal, projectedOverlap,
    spinCoordinate, div_eq_mul_inv]
  ring

lemma tensorOffFresh_eq_block {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (a b : ℝ)
    (hJ : ∀ i ∈ J, eig i = a) (hK : ∀ j ∈ K, eig j = b)
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ) (U : SpecialOrthogonal N) (σ : Fin 3 → X) :
    tensorOffFresh eig J K sp F U σ = tensorOffBlockFresh J K (a-b) sp F U σ := by
  unfold tensorOffFresh
  have he : (∑ i ∈ J, ∑ j ∈ K,
      offCoordinateProduct i j F (specialToOrthogonal U) (sp (σ 0), sp (σ 1)) *
        ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal U) (sp (σ 2)))) =
      ∑ i ∈ J, ∑ j ∈ K, (a-b) *
        (offCoordinateProduct i j F (specialToOrthogonal U) (sp (σ 0), sp (σ 1)) *
          coordinateProduct i j (specialToOrthogonal U) (sp (σ 2))) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hJ i hi, hK j hj]
    ring
  rw [he]
  simp only [← Finset.mul_sum, offCoordinateProduct, coordinateProduct]
  rw [off_coordinate_fresh_sum]
  simp only [tensorOffBlockFresh, ← matrixRotation_specialToOrthogonal, projectedOverlap,
    spinCoordinate]
  ring

end InvariantIsing

end

end OAI
