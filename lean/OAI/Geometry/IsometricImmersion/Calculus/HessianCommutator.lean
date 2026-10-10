import OAI.Geometry.IsometricImmersion.Metrics.MetricSmoothness
import OAI.Geometry.IsometricImmersion.Immersions.InducedMetric
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace HessianCalculus

variable {f h : Coord → ℝ} {p : Coord}

theorem coordPartial_add_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q + h q) p = coordPartial i f p + coordPartial i h p := by
  simp [coordPartial, fderiv_fun_add hf hh]

theorem coordPartial_sub_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q - h q) p = coordPartial i f p - coordPartial i h p := by
  simp [coordPartial, fderiv_fun_sub hf hh]

theorem coordPartial_mul_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q * h q) p =
      coordPartial i f p * h p + f p * coordPartial i h p := by
  simp [coordPartial, fderiv_fun_mul hf hh, add_comm, mul_comm]

theorem coordPartial_sum_two (f : Fin 2 → Coord → ℝ)
    (hf : ∀ a, DifferentiableAt ℝ (f a) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ a, f a q) p = ∑ a, coordPartial i (f a) p := by
  simp only [Fin.sum_univ_two]
  exact coordPartial_add_at (hf 0) (hf 1) i

end HessianCalculus

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem metric_coeff_symm (hg : SmoothPositiveOn g U) (hp : p ∈ U) (i j : Fin 2) :
    g p i j = g p j i := by
  simpa using (hg.2 p hp).1.apply j i

theorem metric_coeff_partial_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k i j : Fin 2) :
    coordPartial k (fun q => g q i j) p = coordPartial k (fun q => g q j i) p := by
  have heq : (fun q => g q i j) =ᶠ[𝓝 p] (fun q => g q j i) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact metric_coeff_symm hg hq i j
  unfold coordPartial
  rw [heq.fderiv_eq]

theorem christoffel_lower_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k i j : Fin 2) :
    christoffel g k i j p = christoffel g k j i p := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [metric_coeff_partial_symm hg hU hp l i j]
  ring

theorem covHessian_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (i j : Fin 2) :
    covHessian g z p i j = covHessian g z p j i := by
  unfold covHessian
  rw [coordPartial_comm hz hU hp i j]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [christoffel_lower_symm hg hU hp a i j]

theorem coordPartial_covHessian (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (i j k : Fin 2) :
    coordPartial i (fun q => covHessian g z q j k) p =
      coordPartial i (coordPartial j (coordPartial k z)) p -
        ∑ a, (coordPartial i (christoffel g a j k) p * coordPartial a z p +
          christoffel g a j k p * coordPartial i (coordPartial a z) p) := by
  have hz1 (a : Fin 2) : DifferentiableAt ℝ (coordPartial a z) p :=
    (((partial_contDiffOn hz hU a) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hg1 (a : Fin 2) : DifferentiableAt ℝ (christoffel g a j k) p :=
    (((christoffel_contDiffOn hg hU a j k) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hz2 : DifferentiableAt ℝ (coordPartial j (coordPartial k z)) p :=
    (((partial_contDiffOn (partial_contDiffOn hz hU k) hU j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hprod (a : Fin 2) : DifferentiableAt ℝ
      (fun q => christoffel g a j k q * coordPartial a z q) p :=
    (hg1 a).mul (hz1 a)
  have hsum : DifferentiableAt ℝ
      (fun q => ∑ a, christoffel g a j k q * coordPartial a z q) p := by
    exact DifferentiableAt.fun_sum fun a _ => hprod a
  change coordPartial i (fun q => coordPartial j (coordPartial k z) q -
      ∑ a, christoffel g a j k q * coordPartial a z q) p = _
  rw [HessianCalculus.coordPartial_sub_at hz2 hsum i,
    HessianCalculus.coordPartial_sum_two
      (fun a q => christoffel g a j k q * coordPartial a z q) hprod i]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  exact HessianCalculus.coordPartial_mul_at (hg1 a) (hz1 a) i

def covDerivHessian (g : MetricField) (z : Coord → ℝ)
    (i j k : Fin 2) (p : Coord) : ℝ :=
  coordPartial i (fun q => covHessian g z q j k) p -
    (∑ a, christoffel g a i j p * covHessian g z p a k) -
    (∑ a, christoffel g a i k p * covHessian g z p j a)

theorem covHessian_commutator (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (i j k : Fin 2) :
    covDerivHessian g z i j k p - covDerivHessian g z j i k p =
      -(∑ a, riemann g a k i j p * coordPartial a z p) := by
  have hGamma (a : Fin 2) : christoffel g a i j p = christoffel g a j i p :=
    christoffel_lower_symm hg hU hp a i j
  unfold covDerivHessian
  rw [coordPartial_covHessian hg hU hz hp i j k,
    coordPartial_covHessian hg hU hz hp j i k,
    coordPartial_comm (partial_contDiffOn hz hU k) hU hp i j]
  simp only [covHessian, riemann, Fin.sum_univ_two]
  rw [hGamma 0, hGamma 1]
  ring

end SmoothLocal.Geometry

end

end OAI
