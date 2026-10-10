import Mathlib
import OAI.Analysis.CoulombIonization.Variational.Spatial

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom
variable {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)

lemma spatial_derivative_square_sum (x : Configuration N) (i : Fin N) (a : Fin 3) :
    (∑ b : Fin N → Fin 2, lineDeriv ℝ (spatialProduct p hp b).value x (direction i a) ^ 2) =
      ∑ h : Fin 2, lineDeriv ℝ (p h).value (x i) (spaceDirections a) ^ 2 := by
  change (∑ b : Fin N → Fin 2, lineDeriv ℝ (spatialProductValue p b) x (direction i a) ^ 2) = _
  simp_rw [spatialProduct_derivative]
  exact binary_product_square_sum (fun k h => (p h).value (x k)) (fun k => hp (x k)) i
    (fun h => lineDeriv ℝ (p h).value (x i) (spaceDirections a))

def spatialErrorWeight (x : Space) : ℝ :=
  ∑ a : Fin 3, ∑ h : Fin 2, lineDeriv ℝ (p h).value x (spaceDirections a) ^ 2

lemma spatial_derivative_density_integrable {ψ : FormVector N} (hψ : SobolevVector ψ)
    (s : Spins N) (i : Fin N) (a : Fin 3) (h : Fin 2) :
    Integrable (fun x : Configuration N =>
      lineDeriv ℝ (p h).value (x i) (spaceDirections a) ^ 2 * ‖ψ.value s x‖ ^ 2) := by
  have hc : Continuous (fun x : Configuration N =>
      lineDeriv ℝ (p h).value (x i) (spaceDirections a)) :=
    ((p h).derivative_continuous a).comp (continuous_apply i)
  have hb : ∃ C, ∀ x : Configuration N,
      |lineDeriv ℝ (p h).value (x i) (spaceDirections a)| ≤ C := by
    obtain ⟨C,hC⟩ := (p h).gradient_bound a
    exact ⟨C,fun x => hC (x i)⟩
  have hh := (memLp_bounded_mul hc hb (hψ.1 s)).norm.integrable_sq
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using hh

lemma spatial_error_weight_integrable {ψ : FormVector N} (hψ : SobolevVector ψ)
    (s : Spins N) (i : Fin N) :
    Integrable (fun x => spatialErrorWeight p (x i) * ‖ψ.value s x‖ ^ 2) := by
  simp only [spatialErrorWeight, Finset.sum_mul]
  exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _
    (fun h _ => spatial_derivative_density_integrable p hψ s i a h))

theorem spatial_cut_error {ψ : FormVector N} (hψ : SobolevVector ψ) :
    (∑ b : Fin N → Fin 2, formMultiplierError (spatialProduct p hp b) ψ) =
      (1 / 2 : ℝ) * ∑ s : Spins N, ∑ i : Fin N,
        ∫ x, spatialErrorWeight p (x i) * ‖ψ.value s x‖ ^ 2 := by
  simp only [formMultiplierError, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  simp only [spatialErrorWeight, Finset.sum_mul]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
    (fun h _ => spatial_derivative_density_integrable p hψ s i a h))]
  apply Finset.sum_congr rfl; intro a _
  rw [← integral_finsetSum _ (fun b _ =>
    smoothMultiplier_gradient_integrable (spatialProduct p hp) b hψ s i a)]
  apply integral_congr_ae (Eventually.of_forall _)
  intro x
  rw [← Finset.sum_mul, spatial_derivative_square_sum p hp, Finset.sum_mul]

theorem spatial_cut_ims {ψ : FormVector N} (hψ : SobolevVector ψ) (Z : ℝ) :
    (∑ b : Fin N → Fin 2, formEnergy Z (multiplyForm (spatialProduct p hp b) ψ)) =
      formEnergy Z ψ + (1 / 2 : ℝ) * ∑ s : Spins N, ∑ i : Fin N,
        ∫ x, spatialErrorWeight p (x i) * ‖ψ.value s x‖ ^ 2 := by
  rw [spatial_cut_energy p hp hψ, spatial_cut_error p hp hψ]

def weightedParticleCount (ψ : FormVector N) (w : Space → ℝ) : ℝ :=
  ∑ s : Spins N, ∑ i : Fin N, ∫ x, w (x i) * ‖ψ.value s x‖ ^ 2

theorem spatial_cut_error_le {ψ : FormVector N} (hψ : SobolevVector ψ)
    (w : Space → ℝ) (hw : Measurable w) {B C : ℝ} (hwB : ∀ x, ‖w x‖ ≤ B)
    (hbound : ∀ x, spatialErrorWeight p x ≤ C * w x) :
    (∑ b : Fin N → Fin 2, formMultiplierError (spatialProduct p hp b) ψ) ≤
      (1 / 2 : ℝ) * C * weightedParticleCount ψ w := by
  rw [spatial_cut_error p hp hψ, weightedParticleCount, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  rw [← integral_const_mul]
  have hi : Integrable (fun x : Configuration N => w (x i) * ‖ψ.value s x‖ ^ 2) :=
    ((hψ.1 s).norm.integrable_sq).bdd_mul
      (hw.comp (measurable_pi_apply i)).aestronglyMeasurable
      (Eventually.of_forall fun x => hwB (x i))
  apply integral_mono (spatial_error_weight_integrable p hψ s i) (hi.const_mul C)
  intro x
  exact (mul_le_mul_of_nonneg_right (hbound (x i)) (sq_nonneg _)).trans_eq (mul_assoc _ _ _)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
