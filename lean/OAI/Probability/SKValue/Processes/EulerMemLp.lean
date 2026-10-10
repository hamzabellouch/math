import Mathlib
import OAI.Probability.SKValue.Equations.RawIncrement
import OAI.Probability.SKValue.Equations.ValueStrip

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma euler_memLp (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (huM : ∀ j<N, Measurable (u (meshTime T N j)))
    (huB : ∀ j<N, ∀ x, |u (meshTime T N j) x|≤1) :
    ∀ j≤N, MemLp (fun z ↦ euler T N γ u z j) 2 (gaussianProduct (Fin (N+1))) := by
  intro j
  induction j with
  | zero => intro _; exact memLp_const (0 : ℝ)
  | succ j ih =>
    intro hj
    have hlt : j<N := by omega
    have hU : MemLp (fun z ↦ u (meshTime T N j) (euler T N γ u z j)) 2
        (gaussianProduct (Fin (N+1))) :=
      MemLp.of_bound ((huM j hlt).comp (measurable_euler T N γ u huM j hlt.le)).aestronglyMeasurable 1
        (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using huB j hlt _))
    exact ((ih hlt.le).add ((gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num)).const_mul _)).add
      (hU.const_mul (stepSize T N*γ (meshTime T N j)))

lemma ValueStrip.value_lipschitz {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : ValueStrip T γ V K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    LipschitzWith 1 (V t) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((h.smooth t ht).differentiable (by norm_num))
  intro x
  exact_mod_cast (show ‖deriv (V t) x‖≤(1 : ℝ) by simpa only [Real.norm_eq_abs] using h.bounded t ht x)

lemma ValueStrip.value_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : ValueStrip T γ V K L)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) T) {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    MemLp (fun ω ↦ V t (Y ω)) 2 μ := by
  have hl : LipschitzWith 1 (fun x ↦ V t x - V t 0) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_sub_right] using (h.value_lipschitz ht).dist_le_mul x y
  have hh := hl.comp_memLp (by simp) hY
  convert hh.add (memLp_const (V t 0)) using 1
  funext ω
  simp

lemma value_mesh_expectation_error {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    |(∫ z, V T (euler T N γ (fun t ↦ deriv (V t)) z N) ∂gaussianProduct (Fin (N+1)))-V 0 0-
      (∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)))| ≤
      Real.sqrt (valueMeshError T N γ V) := by
  let u := fun t ↦ deriv (V t)
  let Y := euler T N γ u
  let μ := gaussianProduct (Fin (N+1))
  let A (i : Fin N) (z : Fin (N+1) → ℝ) := u (meshTime T N i) (Y z i)
  let M (z : Fin (N+1) → ℝ) := ∑ i : Fin N, Real.sqrt (stepSize T N)*A i z*coordinate N i z
  let R (z : Fin (N+1) → ℝ) := valueMeshCompensated T N γ V N z-V 0 0-M z
  have htime (j : ℕ) (hj : j≤N) := mesh_time_mem hT.le hN hj
  have huc (j : ℕ) (hj : j≤N) : Continuous (u (meshTime T N j)) :=
    (h.smooth _ (htime j hj)).continuous_deriv (by norm_num)
  have hY (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ Y z j) :=
    measurable_euler T N γ u (fun i hi ↦ (huc i hi.le).measurable) j hj
  have hAm (i : Fin N) : Measurable (A i) := (huc i i.isLt.le).measurable.comp (hY i i.isLt.le)
  have hAb (i : Fin N) z : |A i z|≤1 := h.bounded _ (htime i i.isLt.le) _
  have hAp (i : Fin N) : DependsBefore i (A i) := eulerCoefficient_dependsBefore T i.isLt.le γ u u
  have hAM (i : Fin N) : MemLp (A i) 2 μ :=
    MemLp.of_bound (hAm i).aestronglyMeasurable 1
      (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hAb i z))
  have hMm : MemLp M 2 μ := finiteRaw_memLp hAm hAp hAM
  have hMv : (∫ z, M z ∂μ)=0 := by
    have hMi (i : Fin N) : Integrable (fun z ↦ Real.sqrt (stepSize T N)*A i z*coordinate N i z) μ :=
      ((rawIncrement_memLp (by omega : (i : ℕ)<N+1) (hAm i) (hAp i) (hAM i)).const_mul
        (Real.sqrt (stepSize T N))).integrable (by norm_num) |>.congr (by
          filter_upwards [] with z; simp only [rawIncrement]; ring)
    rw [show (∫ z, M z ∂μ)=∑ i : Fin N, ∫ z, Real.sqrt (stepSize T N)*A i z*coordinate N i z ∂μ from
      integral_finsetSum _ (fun i _ ↦ hMi i)]
    have he (i : Fin N) : (∫ z, Real.sqrt (stepSize T N)*A i z*coordinate N i z ∂μ)=0 := by
      simp only [mul_assoc]
      rw [integral_const_mul]
      change Real.sqrt (stepSize T N)*(∫ z, rawIncrement (A i) i z ∂μ)=0
      rw [rawIncrement_mean (by omega) (hAm i) (hAp i),mul_zero]
    simp only [he, Finset.sum_const_zero]
  have hEm : MemLp (valueMeshEnergy T N γ V N) 2 μ := by
    apply memLp_finsetSum
    intro j hj
    have hjN : j<N := Finset.mem_range.mp hj
    apply MemLp.const_mul
    apply MemLp.of_bound (((huc j hjN.le).measurable.comp (hY j hjN.le)).pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_pow, sq_le_one_iff_abs_le_one]
    simpa only [abs_abs, u, Function.comp_apply] using h.bounded _ (htime j hjN.le) (Y z j)
  have hYM : MemLp (fun z ↦ Y z N) 2 μ :=
    euler_memLp T N γ u (fun i hi ↦ (huc i hi.le).measurable)
      (fun i hi x ↦ h.bounded _ (htime i hi.le) x) N le_rfl
  have hVM := h.value_memLp (t := T) ⟨hT.le,le_rfl⟩ hYM
  have hlast : meshTime T N N=T := by
    dsimp only [meshTime, stepSize]
    have hn : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
    field_simp
  have hRM : MemLp R 2 μ := by
    dsimp only [R,valueMeshCompensated]
    rw [hlast]
    exact ((hVM.sub hEm).sub (memLp_const (V 0 0))).sub hMm
  have hRint : (∫ z, R z ∂μ)=
      (∫ z, V T (Y z N) ∂μ)-V 0 0-(∫ z, valueMeshEnergy T N γ V N z ∂μ) := by
    dsimp only [R,valueMeshCompensated]
    rw [hlast]
    have hi₁ := integral_sub (((hVM.sub hEm).sub (memLp_const (V 0 0))).integrable (by norm_num)) (hMm.integrable (by norm_num))
    have hi₂ := integral_sub ((hVM.sub hEm).integrable (by norm_num)) (integrable_const (V 0 0))
    simp only [Pi.sub_apply] at hi₁ hi₂
    change (∫ z, V T (Y z N)-valueMeshEnergy T N γ V N z-V 0 0-M z ∂μ)=_
    rw [hi₁, hi₂]
    rw [integral_sub (hVM.integrable (by norm_num)) (hEm.integrable (by norm_num)),hMv,integral_const]
    simp only [probReal_univ, smul_eq_mul, sub_zero]
    ring
  rw [←hRint]
  exact abs_integral_le_integral_abs.trans (integral_abs_le_sqrt_integral_sq hRM)

lemma value_mesh_expectation_error_tendsto {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) :
    Tendsto (fun N ↦ (∫ z, V T (euler T N γ (fun t ↦ deriv (V t)) z N)
      ∂gaussianProduct (Fin (N+1)))-V 0 0-
      (∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)))) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun N ↦ Real.sqrt (valueMeshError T N γ V))
  · filter_upwards [eventually_gt_atTop 0] with N hN
    simpa only [Real.norm_eq_abs] using value_mesh_expectation_error hT h hN
  · simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp (valueMeshError_tendsto_zero hT hT1 h)

end SKValue

end

end OAI
