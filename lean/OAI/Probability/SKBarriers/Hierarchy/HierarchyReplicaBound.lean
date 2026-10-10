import Mathlib
import OAI.Probability.SKBarriers.Scalar.CovarianceRegular
import OAI.Probability.SKBarriers.Hierarchy.HierarchyReplica

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section IntegralTrace
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integral_variance_trace_bound (M Q T : Ω → ℝ)
    (hM : AEMeasurable M μ) (hc : Integrable (fun z => (M z-∫ x, M x ∂μ)^2) μ)
    (hQ : Integrable Q μ) (hT : Integrable T μ) (hT0 : ∀ z, 0 ≤ T z)
    (hp : ∀ z, Q z ≤ (M z-∫ x, M x ∂μ)^2+T z+2*Real.sqrt (T z)) :
    (∫ z, Q z ∂μ) ≤ ProbabilityTheory.variance M μ+(∫ z, T z ∂μ)+2*Real.sqrt (∫ z, T z ∂μ) := by
  have hsm : AEStronglyMeasurable (fun z => Real.sqrt (T z)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hT.aestronglyMeasurable
  have hsq : (fun z => (Real.sqrt (T z))^2) = T := funext (fun z => Real.sq_sqrt (hT0 z))
  have hs2 : MemLp (fun z => Real.sqrt (T z)) 2 μ := by
    rw [memLp_two_iff_integrable_sq hsm,hsq]
    exact hT
  have HI := integral_mono (g := fun z => (M z-∫ x, M x ∂μ)^2+T z+2*Real.sqrt (T z)) hQ
    ((hc.add hT).add ((hs2.integrable (by norm_num)).const_mul 2)) hp
  have hs := integral_sqrt_le_sqrt_integral T hT hT0
  rw [integral_add (f := fun z => (M z-∫ x, M x ∂μ)^2+T z) (g := fun z => 2*Real.sqrt (T z))
    (hc.add hT) ((hs2.integrable (by norm_num)).const_mul 2),
    integral_add hc hT,integral_const_mul,← variance_eq_integral hM] at HI
  linarith
end IntegralTrace

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section HierarchyReplicaBound
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyOverlap_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ)
    (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) :
    Integrable (fun z => finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)^2))
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  apply Integrable.of_bound (finiteReplicaMoment_continuous _
    (fun s => (hierarchySpinWeight_regular n m U j s).1) _).aestronglyMeasurable 4
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyOverlap_integrand_bounds n m U v hv j z).1]
    exact (hierarchyOverlap_integrand_bounds n m U v hv j z).2

theorem hierarchyMeanSquare_centered_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ)
    (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) :
    Integrable (fun z => (hierarchyMeanSquare n m U (fun i s => v s i) j z-
      hierarchyMeanOverlap n m U (fun i s => v s i) j)^2)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  let M := hierarchyMeanSquare n m U (fun i s => v s i) j
  let r := hierarchyMeanOverlap n m U (fun i s => v s i) j
  have hc (i : Fin N) (s : S) : ‖v s i‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using hv s i
  have hM : Continuous M := hierarchyMeanSquare_continuous n m U _ hc j
  have hr := hierarchyMeanOverlap_bounds n m U _ hc j
  refine Integrable.of_bound (f := fun z => (M z-r)^2) ?_ 1 ?_
  · exact ((hM.sub continuous_const).pow 2).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖(M z-r)^2‖ ≤ 1
    have hz := hierarchyMeanSquare_bounds n m U _ hc j z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),sq_le_one_iff_abs_le_one]
    exact abs_le.2 ⟨by linarith [hr.1,hr.2,hz.1,hz.2],
      by linarith [hr.1,hr.2,hz.1,hz.2]⟩

theorem hierarchyOverlap_integrand_le {N : ℕ} (hN : 0 < N) (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ)
    (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) (z : ParameterSpace n) :
    let M := hierarchyMeanSquare n m U (fun i s => v s i) j z
    let r := hierarchyMeanOverlap n m U (fun i s => v s i) j
    let T := hierarchyTraceSquare n m U v j z/(N : ℝ)^2
    finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t)-r)^2) ≤ (M-r)^2+T+2*Real.sqrt T := by
  dsimp only
  rw [finiteReplicaMoment_variance_split _ (hierarchySpinWeight_sum n m U j z),finiteReplicaMoment_normalizedDot,
    hierarchyMeanSquare_eq_finiteMean]
  have H := finiteReplica_normalized_variance_le hN _ v
    (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z) hv
  dsimp only [hierarchyTraceSquare]
  linarith

theorem hierarchyOverlapError_le {N : ℕ} (hN : 0 < N) (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ)
    (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) :
    let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
    let B := (∫ z, hierarchyTraceSquare n m U v j z ∂μ)/(N : ℝ)^2
    hierarchyOverlapError n m U v j ≤
      ProbabilityTheory.variance (hierarchyMeanSquare n m U (fun i s => v s i) j) μ+B+2*Real.sqrt B := by
  let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  have hc (i : Fin N) (s : S) : ‖v s i‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using hv s i
  have H := integral_variance_trace_bound (μ := μ)
    (hierarchyMeanSquare n m U (fun i s => v s i) j)
    (fun z => finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)^2))
    (fun z => hierarchyTraceSquare n m U v j z/(N : ℝ)^2)
    (hierarchyMeanSquare_continuous n m U _ hc j).measurable.aemeasurable
    (hierarchyMeanSquare_centered_integrable n m U v hv j)
    (hierarchyOverlap_integrable n m U v hv j)
    ((hierarchyTraceSquare_integrable n m U v hv j 0).div_const _)
    (fun z => div_nonneg (finiteCovariance_trace_square_nonneg _ v
      (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z)) (sq_nonneg _))
    (hierarchyOverlap_integrand_le hN n m U v hv j)
  rw [integral_div] at H
  exact H
end HierarchyReplicaBound
end SK.Analytic

end
end

end

end OAI
