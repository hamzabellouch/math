import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.SobolevVector
import OAI.Analysis.CoulombIonization.Variational.Pointwise

namespace OAI

noncomputable section

namespace CoulombAtom

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
section
variable {N : ℕ} {J : Type*} [Fintype J]
variable (p : J → SmoothMultiplier (sectorDirections N))
variable (hp : ∀ x, ∑ j, (p j).value x ^ 2 = 1)
include hp

lemma finite_partition_value (ψ : FormVector N) (s : Spins N) (x : Configuration N) :
    ∑ j, ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 = ‖ψ.value s x‖ ^ 2 :=
  finite_complex_partition (fun j => (p j).value x) (hp x) _

lemma finite_partition_gradient (ψ : FormVector N) (s : Spins N)
    (i : Fin N) (a : Fin 3) (x : Configuration N) :
    (∑ j, ‖(multiplyForm (p j) ψ).gradient s i a x‖ ^ 2) =
      ‖ψ.gradient s i a x‖ ^ 2 +
        (∑ j, lineDeriv ℝ (p j).value x (direction i a) ^ 2) * ‖ψ.value s x‖ ^ 2 := by
  exact finite_complex_ims _ _ (hp x)
    (square_partition_derivative _ (fun j => (p j).regular.differentiable (by simp))
      hp x (direction i a)) _ _

lemma finite_partition_mass {ψ : FormVector N} (hψ : SobolevVector ψ) :
    ∑ j, formMass (multiplyForm (p j) ψ) = formMass ψ := by
  unfold formMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← integral_finsetSum _ (fun j _ => ((hψ.multiply (p j)).1 s).norm.integrable_sq)]
  exact integral_congr_ae (Eventually.of_forall (finite_partition_value p hp ψ s))

omit hp [Fintype J] in
lemma smoothMultiplier_gradient_integrable (j : J) {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (i : Fin N) (a : Fin 3) :
    Integrable (fun x => lineDeriv ℝ (p j).value x (direction i a) ^ 2 *
      ‖ψ.value s x‖ ^ 2) := by
  have hh := (memLp_bounded_mul ((p j).derivative_continuous (i,a))
    ((p j).gradient_bound (i,a)) (hψ.1 s)).norm.integrable_sq
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using hh

lemma finite_partition_kinetic {ψ : FormVector N} (hψ : SobolevVector ψ)
    (s : Spins N) (i : Fin N) (a : Fin 3) :
    (∑ j, ∫ x, ‖(multiplyForm (p j) ψ).gradient s i a x‖ ^ 2) =
      (∫ x, ‖ψ.gradient s i a x‖ ^ 2) +
        ∑ j, ∫ x, lineDeriv ℝ (p j).value x (direction i a) ^ 2 *
          ‖ψ.value s x‖ ^ 2 := by
  rw [← integral_finsetSum _ (fun j _ =>
    ((hψ.multiply (p j)).2.1 s i a).norm.integrable_sq)]
  have he : (fun x => ∑ j, ‖(multiplyForm (p j) ψ).gradient s i a x‖ ^ 2) =
      fun x => ‖ψ.gradient s i a x‖ ^ 2 +
        ∑ j, lineDeriv ℝ (p j).value x (direction i a) ^ 2 * ‖ψ.value s x‖ ^ 2 := by
    funext x
    rw [finite_partition_gradient p hp, Finset.sum_mul]
  rw [he, integral_add (hψ.2.1 s i a).norm.integrable_sq
      (integrable_finsetSum _ (fun j _ => smoothMultiplier_gradient_integrable p j hψ s i a)),
    integral_finsetSum _ (fun j _ => smoothMultiplier_gradient_integrable p j hψ s i a)]

lemma finite_partition_div_integral (ψ : FormVector N) (s : Spins N)
    (w : Configuration N → ℝ)
    (hi : ∀ j, Integrable (fun x => ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 / w x)) :
    (∑ j, ∫ x, ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 / w x) =
      ∫ x, ‖ψ.value s x‖ ^ 2 / w x := by
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [← Finset.sum_div, finite_partition_value p hp]

lemma finite_partition_nuclear {ψ : FormVector N} (hψ : SobolevVector ψ)
    (s : Spins N) (i : Fin N) :
    (∑ j, ∫ x, ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 / ‖x i‖) =
      ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖ :=
  finite_partition_div_integral p hp ψ s _
    (fun j => (hψ.multiply (p j)).nuclear_integrable s i)

lemma finite_partition_pair {ψ : FormVector N} (hψ : SobolevVector ψ)
    (s : Spins N) (i k : Fin N) (hik : i ≠ k) :
    (∑ j, ∫ x, ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 / ‖x i - x k‖) =
      ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x k‖ :=
  finite_partition_div_integral p hp ψ s _
    (fun j => (hψ.multiply (p j)).pair_integrable s i k hik)

def formMultiplierError (q : SmoothMultiplier (sectorDirections N)) (ψ : FormVector N) : ℝ :=
  (1 / 2 : ℝ) * ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
    ∫ x, lineDeriv ℝ q.value x (direction i a) ^ 2 * ‖ψ.value s x‖ ^ 2

theorem finite_partition_energy {ψ : FormVector N} (hψ : SobolevVector ψ) (Z : ℝ) :
    (∑ j, formEnergy Z (multiplyForm (p j) ψ)) =
      formEnergy Z ψ + ∑ j, formMultiplierError (p j) ψ := by
  have hk : (∑ j, ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ∫ x, ‖(multiplyForm (p j) ψ).gradient s i a x‖ ^ 2) =
      (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖ψ.gradient s i a x‖ ^ 2) +
      ∑ j, ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ∫ x, lineDeriv ℝ (p j).value x (direction i a) ^ 2 * ‖ψ.value s x‖ ^ 2 := by
    calc
      _ = ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
          ∑ j, ∫ x, ‖(multiplyForm (p j) ψ).gradient s i a x‖ ^ 2 := by
        rw [Finset.sum_comm]
        congr 1; funext s
        rw [Finset.sum_comm]
        congr 1; funext i
        rw [Finset.sum_comm]
      _ = _ := by
        simp_rw [finite_partition_kinetic p hp hψ, Finset.sum_add_distrib]
        congr 1
        symm
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro s _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_comm]
  have hn : (∑ j, ∑ s : Spins N, ∑ i : Fin N,
      ∫ x, ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 / ‖x i‖) =
      ∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => finite_partition_nuclear p hp hψ s i)
  have hv : (∑ j, ∑ s : Spins N, ∑ i : Fin N, ∑ k : Fin N,
      if i < k then ∫ x, ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 / ‖x i - x k‖ else 0) =
      ∑ s : Spins N, ∑ i : Fin N, ∑ k : Fin N,
        if i < k then ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x k‖ else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    split_ifs with hik
    · exact finite_partition_pair p hp hψ s i k (ne_of_lt hik)
    · simp
  simp only [formEnergy, formMultiplierError, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hk, hn, hv]
  ring

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

def spaceDirections (a : Fin 3) : Space := EuclideanSpace.single a 1

end CoulombAtom

end

end OAI
