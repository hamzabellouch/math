import OAI.Geometry.IsometricImmersion.Assembly.SupportedNeighborhoods
import OAI.Geometry.IsometricImmersion.Assembly.SupportedMetricJets
import Mathlib.Topology.Closure

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise Distributions

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

@[simp] theorem perturbationSeminorm_zero (k : ℕ) :
    perturbationSeminorm k 0 = 0 := map_zero (perturbationSeminormFamily k)

theorem closure_exists_finite_seminorm_approximation
    {T : Type*} [TopologicalSpace T] (f : T → SymmetricPerturbation) (hf : Continuous f)
    {A : Set T} {theta : T} (hclosure : theta ∈ closure A)
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta ∈ A, ∀ k ≤ n, perturbationSeminorm k (f eta - f theta) < epsilon := by
  let O : Set T := {eta | ∀ k : Fin (n + 1),
    perturbationSeminorm k.val (f eta - f theta) < epsilon}
  have hO : IsOpen O := by
    change IsOpen {eta | ∀ k : Fin (n + 1),
      perturbationSeminorm k.val (f eta - f theta) < epsilon}
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_lt ((perturbationSeminorm_continuous k.val).comp
      (hf.sub continuous_const)) continuous_const
  have htheta : theta ∈ O := by
    intro k
    simpa only [sub_self, perturbationSeminorm_zero] using hepsilon
  obtain ⟨eta, hetaO, hetaA⟩ := mem_closure_iff.mp hclosure O hO htheta
  refine ⟨eta, hetaA, ?_⟩
  intro k hk
  exact hetaO ⟨k, by omega⟩

theorem metricCoefficientCLM_norm_le (i j : Fin 2) :
    ‖(show (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ from metricCoefficientCLM i j)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  exact (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

theorem perturbation_coefficient_derivative_norm_le
    (eta : SymmetricPerturbation) (k : ℕ) (p : Coord) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ k (fun x => perturbationTensor eta x i j) p‖ ≤
      perturbationSeminorm k eta := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    ((norm_nonneg _).trans (perturbation_derivative_norm_le eta k p))
  intro v
  change ‖iteratedFDeriv ℝ k (fun x => eta.val x i j) p v‖ ≤ _
  rw [supportedTensor_coeff_iteratedFDeriv]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k eta.val p v‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ ‖iteratedFDeriv ℝ k eta.val p‖ * ∏ l, ‖v l‖ :=
      (iteratedFDeriv ℝ k eta.val p).le_opNorm v
    _ ≤ perturbationSeminorm k eta * ∏ l, ‖v l‖ :=
      mul_le_mul_of_nonneg_right (perturbation_derivative_norm_le eta k p)
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))

theorem perturbedMetric_sub_eq_tensor_sub (g0 : MetricField) (eta theta : SymmetricPerturbation) :
    (fun p => perturbedMetric g0 eta p - perturbedMetric g0 theta p) =
      perturbationTensor (eta - theta) := by
  funext p
  ext i j
  change (g0 p i j + perturbationTensor eta p i j) -
    (g0 p i j + perturbationTensor theta p i j) =
      perturbationTensor eta p i j - perturbationTensor theta p i j
  ring

theorem perturbedMetric_coefficient_sub_eq (g0 : MetricField)
    (eta theta : SymmetricPerturbation) (i j : Fin 2) :
    (fun p => perturbedMetric g0 eta p i j - perturbedMetric g0 theta p i j) =
      (fun p => perturbationTensor (eta - theta) p i j) := by
  funext p
  exact congrFun (congrFun (congrFun (perturbedMetric_sub_eq_tensor_sub g0 eta theta) p) i) j

theorem closure_exists_metric_jet_approximation
    {T : Type*} [TopologicalSpace T] (f : T → SymmetricPerturbation) (hf : Continuous f)
    (g0 : MetricField) {A : Set T} {theta : T} (hclosure : theta ∈ closure A)
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta ∈ A,
      (∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 (f eta) x -
          perturbedMetric g0 (f theta) x) p‖ ≤ epsilon) ∧
      (∀ i j : Fin 2, ∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 (f eta) x i j -
          perturbedMetric g0 (f theta) x i j) p‖ ≤ epsilon) := by
  obtain ⟨eta, heta, hsmall⟩ := closure_exists_finite_seminorm_approximation f hf hclosure n hepsilon
  refine ⟨eta, heta, ?_, ?_⟩
  · intro k hk p
    rw [perturbedMetric_sub_eq_tensor_sub]
    exact (perturbation_derivative_norm_le (f eta - f theta) k p).trans (hsmall k hk).le
  · intro i j k hk p
    rw [perturbedMetric_coefficient_sub_eq]
    exact (perturbation_coefficient_derivative_norm_le (f eta - f theta) k p i j).trans (hsmall k hk).le

theorem closure_exists_metric_jet_approximation_with_witness
    {T H : Type*} [TopologicalSpace T] (f : T → SymmetricPerturbation) (hf : Continuous f)
    (g0 : MetricField) (P : T → H → Prop) {theta : T}
    (hclosure : theta ∈ closure {eta | ∃ h : H, P eta h})
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (eta : T) (h : H), P eta h ∧
      (∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 (f eta) x -
          perturbedMetric g0 (f theta) x) p‖ ≤ epsilon) ∧
      (∀ i j : Fin 2, ∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 (f eta) x i j -
          perturbedMetric g0 (f theta) x i j) p‖ ≤ epsilon) := by
  obtain ⟨eta, ⟨h, hP⟩, hT, hC⟩ :=
    closure_exists_metric_jet_approximation f hf g0 hclosure n hepsilon
  exact ⟨eta, h, hP, hT, hC⟩

end SmoothLocal.Perturbation

end

end OAI
