import OAI.Probability.InvariantIsing.Arrays.TensorDiagonalWardCorrectionBound
import OAI.Probability.InvariantIsing.Arrays.TensorWardReplica

namespace OAI

/-! The direct and fresh principal Ward observables retain only the spin
projection of the state. They therefore agree on every finite leaf cutoff. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*}

def tensorOffDirect {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ)
    (U : SpecialOrthogonal N) (σ : Fin 2 → X) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
    (offCoordinateVariation i j F (specialToOrthogonal U) (sp (σ 0), sp (σ 1)) +
      offCoordinateProduct i j F (specialToOrthogonal U) (sp (σ 0), sp (σ 1)) *
        ((eig i - eig j) * (coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) +
          coordinateProduct i j (specialToOrthogonal U) (sp (σ 1)))))

def tensorOffFresh {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ)
    (U : SpecialOrthogonal N) (σ : Fin 3 → X) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
    offCoordinateProduct i j F (specialToOrthogonal U) (sp (σ 0), sp (σ 1)) *
      ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal U) (sp (σ 2)))

def tensorOffDirectCap {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (B : ℝ) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
    (2 * N * B + (N * B) * (|eig i - eig j| * (2 * N)))

def tensorOffFreshCap {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (B : ℝ) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, (N * B) * (|eig i - eig j| * N)

lemma tensorOffDirectCap_nonneg {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    {B : ℝ} (hB : 0 ≤ B) : 0 ≤ tensorOffDirectCap eig J K B := by
  unfold tensorOffDirectCap
  positivity

lemma tensorOffFreshCap_nonneg {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    {B : ℝ} (hB : 0 ≤ B) : 0 ≤ tensorOffFreshCap eig J K B := by
  unfold tensorOffFreshCap
  positivity

lemma offCoordinateProduct_abs_le {N : ℕ} (i j : Fin N) (U : Orthogonal N)
    (F : Spin N → Spin N → ℝ) {B : ℝ} (hF : ∀ σ τ, |F σ τ| ≤ B) (σ τ : Spin N) :
    |offCoordinateProduct i j F U (σ,τ)| ≤ N * B := by
  unfold offCoordinateProduct
  rw [abs_mul]
  exact mul_le_mul (abs_crossCoordinateProduct_le i j U σ τ) (hF σ τ)
    (abs_nonneg _) (Nat.cast_nonneg _)

lemma offCoordinateVariation_abs_le {N : ℕ} (i j : Fin N) (U : Orthogonal N)
    (F : Spin N → Spin N → ℝ) {B : ℝ}
    (hF : ∀ σ τ, |F σ τ| ≤ B) (σ τ : Spin N) :
    |offCoordinateVariation i j F U (σ,τ)| ≤ 2 * N * B := by
  unfold offCoordinateVariation
  rw [abs_mul]
  have hd := (abs_sub _ _).trans (add_le_add
    (abs_crossCoordinateProduct_le j j U σ τ) (abs_crossCoordinateProduct_le i i U σ τ))
  have hd' : |spinCoordinate U σ j * spinCoordinate U τ j -
      spinCoordinate U σ i * spinCoordinate U τ i| ≤ 2 * N := by linarith
  exact mul_le_mul hd' (hF σ τ) (abs_nonneg _) (by positivity)

lemma tensorOffDirect_abs_le {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ σ τ, |F σ τ| ≤ B) (U : SpecialOrthogonal N) (σ : Fin 2 → X) :
    |tensorOffDirect eig J K sp F U σ| ≤ tensorOffDirectCap eig J K B := by
  unfold tensorOffDirect tensorOffDirectCap
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (abs_add_le _ _).trans
  apply add_le_add (offCoordinateVariation_abs_le i j (specialToOrthogonal U) F hF _ _)
  rw [abs_mul, abs_mul]
  apply mul_le_mul (offCoordinateProduct_abs_le i j _ F hF _ _) _ (by positivity) (by positivity)
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hs := (abs_add_le _ _).trans (add_le_add
    (abs_coordinateProduct_le i j (specialToOrthogonal U) (sp (σ 0)))
    (abs_coordinateProduct_le i j (specialToOrthogonal U) (sp (σ 1))))
  linarith

lemma tensorOffFresh_abs_le {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ σ τ, |F σ τ| ≤ B) (U : SpecialOrthogonal N) (σ : Fin 3 → X) :
    |tensorOffFresh eig J K sp F U σ| ≤ tensorOffFreshCap eig J K B := by
  unfold tensorOffFresh tensorOffFreshCap
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul, abs_mul]
  exact mul_le_mul (offCoordinateProduct_abs_le i j _ F hF _ _)
    (mul_le_mul_of_nonneg_left (abs_coordinateProduct_le i j _ (sp (σ 2))) (abs_nonneg _))
    (by positivity) (by positivity)

lemma measurable_tensorOffDirect_at {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ) (σ : Fin 2 → X) :
    Measurable (fun U => tensorOffDirect eig J K sp F U σ) := by
  unfold tensorOffDirect offCoordinateVariation offCoordinateProduct coordinateProduct
  have hc (s : X) (a : Fin N) :=
    (measurable_spinCoordinate (sp s) a).comp measurable_specialToOrthogonal
  exact (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    ((((hc (σ 0) j).mul (hc (σ 1) j)).sub ((hc (σ 0) i).mul (hc (σ 1) i))).mul_const _).add
      ((((hc (σ 0) i).mul (hc (σ 1) j)).mul_const _).mul
        ((((hc (σ 0) i).mul (hc (σ 0) j)).add ((hc (σ 1) i).mul (hc (σ 1) j))).const_mul _))).const_mul _

lemma measurable_tensorOffFresh_at {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ) (σ : Fin 3 → X) :
    Measurable (fun U => tensorOffFresh eig J K sp F U σ) := by
  unfold tensorOffFresh offCoordinateProduct coordinateProduct
  have hc (s : X) (a : Fin N) :=
    (measurable_spinCoordinate (sp s) a).comp measurable_specialToOrthogonal
  exact (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (((hc (σ 0) i).mul (hc (σ 1) j)).mul_const _).mul
      (((hc (σ 2) i).mul (hc (σ 2) j)).const_mul _)).const_mul _

lemma measurable_tensorOffDirect [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (sp : X → Spin N)
    (F : Spin N → Spin N → ℝ) :
    Measurable (Function.uncurry (tensorOffDirect eig J K sp F)) :=
  measurable_from_prod_countable_left (fun σ => measurable_tensorOffDirect_at eig J K sp F σ)

lemma measurable_tensorOffFresh [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (sp : X → Spin N)
    (F : Spin N → Spin N → ℝ) :
    Measurable (Function.uncurry (tensorOffFresh eig J K sp F)) :=
  measurable_from_prod_countable_left (fun σ => measurable_tensorOffFresh_at eig J K sp F σ)

end InvariantIsing

end

end OAI
