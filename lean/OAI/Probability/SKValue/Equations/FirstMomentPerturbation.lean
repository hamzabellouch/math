import Mathlib
import OAI.Probability.SKValue.Equations.ShiftedPairing
import OAI.Probability.SKValue.Gaussian.CoupledCoordinates

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

lemma first_moment_perturbation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g e : Ω → ℝ} {L : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (he : MemLp e 2 μ) (hL : 0≤L)
    (hbound : ∀ᵐ ω ∂μ, |f ω-g ω|≤L*|e ω|) :
    |(∫ ω, f ω ∂μ)-(∫ ω, g ω ∂μ)|≤L*Real.sqrt (∫ ω, (e ω)^2 ∂μ) := by
  have hfi := hf.integrable (by norm_num : (1 : ENNReal)≤2)
  have hgi := hg.integrable (by norm_num : (1 : ENNReal)≤2)
  have hei := he.integrable (by norm_num : (1 : ENNReal)≤2)
  calc
    _ = |∫ ω, f ω-g ω ∂μ| := by rw [integral_sub hfi hgi]
    _ ≤ ∫ ω, |f ω-g ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, L*|e ω| ∂μ := integral_mono_ae (hfi.sub hgi).abs (hei.abs.const_mul L) hbound
    _ = L*(∫ ω, |e ω| ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq he) hL

lemma coupled_mesh_error_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) : MemLp (meshMaxError T X (coupledEuler T γ u B) N) 2 μ := by
  apply MemLp.of_bound (meshMaxError_measurable_on hT.le hXM (coupled_euler_measurable hB hT h) N) (2*T*γ T)
  filter_upwards [hpaths] with ω hω
  have hδ : 0≤T/(N : ℝ) := div_nonneg hT.le (Nat.cast_nonneg N)
  have hmesh : (N : ℝ)*(T/N)=T := by field_simp
  have hb := driven_euler_uniform_bound (Y := fun j ↦ coupledEuler T γ u B N j ω)
    hδ hT.le hmesh h.gamma_mono (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩)
    h.bounded hω.1 hω.2 (coupled_euler_zero T γ u B N ω)
    (fun j hj ↦ coupled_euler_step B hT γ u hN hj ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (meshMaxError_nonneg T X (coupledEuler T γ u B) N ω)]
  exact initialMax_le_iff.mpr hb

lemma coupled_mesh_moment_bounds {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L D La : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hD0 : 0≤D) (hLa : 0≤La)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (hLip : ∀ t∈Icc (0 : ℝ) T, ∀ x y, |deriv (u t) x-deriv (u t) y|≤La*|x-y|)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) (j : Fin N)
    (hmom : (∫ ω, (deriv (u (meshTime T N j)) (X (meshTime T N j) ω))^2 ∂μ)=1) :
    |(∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1)))-1|≤
      (2*D*La)*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) ∧
    |(∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1)))-
      ∫ ω, deriv (u (meshTime T N j)) (X (meshTime T N j) ω) ∂μ|≤
      La*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) := by
  let t := meshTime T N j
  let F (ω : Ω) := deriv (u t) (coupledEuler T γ u B N j ω)
  let G (ω : Ω) := deriv (u t) (X t ω)
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht : t∈Icc (0 : ℝ) T := mesh_time_mem hT.le hN j.isLt.le
  have hd : Continuous (deriv (u t)) := (h.smooth t ht).continuous_deriv (by norm_num)
  have hFM : MemLp F 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (coupled_euler_measurable hB hT h N j j.isLt.le).aemeasurable).aestronglyMeasurable D
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, F] using hD t ht _))
  have hGM : MemLp G 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (hXM t ht).aemeasurable).aestronglyMeasurable D
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, G] using hD t ht _))
  have hEM : MemLp E 2 μ := coupled_mesh_error_memLp hB hT h hXM hpaths hN
  have hFG (ω : Ω) : |F ω-G ω|≤La*|E ω| := by
    have he : |coupledEuler T γ u B N j ω-X t ω|≤E ω :=
      le_initialMax (f := fun k ↦ |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) j.isLt.le
    calc
      _ ≤ La*|coupledEuler T γ u B N j ω-X t ω| := hLip t ht _ _
      _ ≤ La*(E ω) := mul_le_mul_of_nonneg_left he hLa
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) hLa
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have hmraw := mesh_raw_measurable hT.le h hN j.isLt.le
  have heq1 : (∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1)))=∫ ω, F ω ∂μ := by
    rw [←hlaw.integral_comp hmraw.aestronglyMeasurable]
    simp only [Function.comp_apply, F, meshRaw, t, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)]
  have heq2 : (∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1)))=∫ ω, (F ω)^2 ∂μ := by
    rw [←hlaw.integral_comp (hmraw.pow_const 2).aestronglyMeasurable]
    simp only [Function.comp_apply, F, meshRaw, t, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)]
  constructor
  · rw [heq2, ←hmom]
    exact second_moment_perturbation hFM hGM hEM hD0 hLa
      (Eventually.of_forall (fun ω ↦ ⟨hD t ht _,hD t ht _,hFG ω⟩))
  · rw [heq1]
    exact first_moment_perturbation hFM hGM hEM hLa (Eventually.of_forall hFG)

end SKValue

end

end OAI
