import Mathlib
import OAI.Probability.SKValue.Processes.MeshMeanBound
import OAI.Probability.SKValue.Equations.FirstMomentPerturbation

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma mean_derivative_continuous {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℝ → Ω → ℝ} {T D La : ℝ} {u : ℝ → ℝ → ℝ}
    (hLa : 0≤La)
    (hd : ∀ t∈Icc (0 : ℝ) T, Continuous (deriv (u t)))
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hXC : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T)) :
    ContinuousOn (fun t ↦ ∫ ω, deriv (u t) (X t ω) ∂μ) (Icc (0 : ℝ) T) := by
  have hj : ContinuousOn (fun p : ℝ×ℝ ↦ deriv (u p.1) p.2)
      {p | p.1∈Icc (0 : ℝ) T} := by
    apply (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (2*La)) ?_).continuousOn
    intro p hp q hq
    rw [Real.coe_toNNReal _ (by positivity), Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    calc
      _ ≤ La*(|p.1-q.1|+|p.2-q.2|) := hLip p.1 hp q.1 hq p.2 q.2
      _ ≤ _ := by
        have h₁ := le_max_left |p.1-q.1| |p.2-q.2|
        have h₂ := le_max_right |p.1-q.1| |p.2-q.2|
        nlinarith
  apply continuousOn_of_dominated (bound := fun _ ↦ D)
  · intro t ht
    exact ((hd t ht).measurable.comp_aemeasurable (hXM t ht).aemeasurable).aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hD t ht (X t ω))
  · exact integrable_const D
  · filter_upwards [hXC] with ω hω
    exact hj.comp (continuousOn_id.prodMk hω) (fun t ht ↦ ht)

theorem finiteGaussian_from_diffusion
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L D Lu La : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L)
    (hD0 : 0≤D) (hLu : 0≤Lu) (hLa : 0≤La)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (huLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (haLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0 : ℝ) T, X t ω = B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    (hmom : ∀ t∈Icc (0 : ℝ) T, (∫ ω, (deriv (u t) (X t ω))^2 ∂μ)=1) :
    (∀ᶠ N in atTop, ∀ j<N, 0<predictableNormalizer (meshRaw T N γ u j)
      (gaussianProduct (Fin (N+1)))) ∧
    Tendsto (fun N ↦ finiteShiftedValue T N γ u) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, deriv (u t) (X t ω) ∂μ)) := by
  let E (N : ℕ) := ∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ
  let r (N : ℕ) := (2*D*La+La)*Real.sqrt (E N)
  have hr (N : ℕ) : 0≤r N := mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hE : Tendsto E atTop (𝓝 0) := coupled_euler_L2_convergence hB hT h hLu huLip hXM hpaths
  have hr0 : Tendsto r atTop (𝓝 0) := by
    simpa only [r, Real.sqrt_zero, mul_zero, Function.comp_def] using
      ((Real.continuous_sqrt.tendsto 0).comp hE).const_mul (2*D*La+La)
  have hbounds (N : ℕ) (hN : 0<N) (j : Fin N) :=
    coupled_mesh_moment_bounds hB hT h hD0 hLa hD
      (fun t ht x y ↦ by simpa only [sub_self, abs_zero, zero_add] using haLip t ht t ht x y)
      hXM (hpaths.mono (fun _ hω ↦ hω.2.2)) hN j
      (hmom _ (mesh_time_mem hT.le hN j.isLt.le))
  apply finiteGaussian_from_strip_and_moments hT hT1 h hD0 hD
    (mean_derivative_continuous hLa (fun t ht ↦ (h.smooth t ht).continuous_deriv (by norm_num))
      hD haLip hXM (hpaths.mono (fun _ hω ↦ hω.1))) hr hr0
  · intro N hN j
    exact (hbounds N hN j).1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hLa) (Real.sqrt_nonneg _))
  · intro N hN j
    exact (hbounds N hN j).2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (Real.sqrt_nonneg _))

end SKValue

end

end OAI
