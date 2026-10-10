import Mathlib
import OAI.Probability.SKValue.Control.ControlVerification
import OAI.Probability.SKValue.Processes.Feedback

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma coupledCoordinates_measurable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, StronglyMeasurable (B t)) (T : ℝ) (N : ℕ) :
    Measurable (coupledCoordinates T N B) := by
  apply Measurable.of_eval
  intro j
  exact ((hBm _).measurable.sub (hBm _).measurable).div_const _

lemma ValueStrip.mesh_energy_memLp {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0 ≤ T) (h : ValueStrip T γ V K L) (N : ℕ) :
    MemLp (valueMeshEnergy T N γ V N) 2 (gaussianProduct (Fin (N+1))) := by
  have hu (j : ℕ) (hj : j ≤ N) : Measurable (deriv (V (meshTime T N j))) :=
    ((h.smooth _ (mesh_time_mem_total hT hj)).continuous_deriv (by norm_num)).measurable
  apply memLp_finsetSum
  intro j hj
  have hjN : j<N := Finset.mem_range.mp hj
  apply MemLp.const_mul
  apply MemLp.of_bound
    (((hu j hjN.le).comp (measurable_euler T N γ (fun t ↦ deriv (V t))
      (fun i hi ↦ hu i hi.le) j hjN.le)).pow_const 2).aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),sq_le_one_iff_abs_le_one]
  exact h.bounded _ (mesh_time_mem_total hT hjN.le) _

lemma ValueStrip.feedback_payoff_approximation
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) (hγM : Measurable γ)
    {N : ℕ} (hN : 0<N) :
    |(∫ ω, V T (controlState B γ (feedbackControl B γ V T N) 0 T ω)-
      (1/2 : ℝ)*controlAccum γ (feedbackControl B γ V T N) 2 T ω ∂μ)-
      ((∫ z, V T (euler T N γ (fun t ↦ deriv (V t)) z N) ∂gaussianProduct (Fin (N+1)))-
        ∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)))| ≤
      (3/2 : ℝ)*stepSize T N*(γ T-γ 0) := by
  let α := feedbackControl B γ V T N
  let Z := coupledCoordinates T N B
  let F := fun ω ↦ V T (controlState B γ α 0 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω
  let G := fun ω ↦ V T (coupledEuler T γ (fun t ↦ deriv (V t)) B N N ω)-
    valueMeshEnergy T N γ V N (Z ω)
  have ht : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hα := h.feedback_progressive hBm hT hN
  have hαb := h.feedback_bound B hT.le N
  have hγb (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : |γ t| ≤ γ T := by
    rw [abs_of_nonneg (h.gamma_nonneg t ht)]
    exact h.gamma_mono ht ⟨hT.le,le_rfl⟩ ht.2
  have hXi := controlState_memLp_two hB hBm hα hαb hγM hγb 0 hT.le le_rfl
  have hVi := (h.value_memLp ht hXi).integrable (by norm_num)
  have hAi := controlAccum_integrable (μ := μ) hα hαb hγM hγb 2 hT.le le_rfl
  have hFi : Integrable F μ := hVi.sub (hAi.const_mul (1/2))
  have huc (j : ℕ) (hj : j ≤ N) : Measurable (deriv (V (meshTime T N j))) :=
    ((h.smooth _ (mesh_time_mem_total hT.le hj)).continuous_deriv (by norm_num)).measurable
  have hY := euler_memLp T N γ (fun t ↦ deriv (V t)) (fun j hj ↦ huc j hj.le)
    (fun j hj x ↦ h.bounded _ (mesh_time_mem_total hT.le hj.le) x) N le_rfl
  have hV := h.value_memLp ht hY
  have hE := h.mesh_energy_memLp hT.le N
  have hZlaw := coupledCoordinates_hasLaw hB hT hN
  have hZmp := hZlaw.measurePreserving (coupledCoordinates_measurable hBm T N)
  have hGi : Integrable G μ := by
    have hh := ((hV.sub hE).comp_measurePreserving hZmp).integrable (by norm_num)
    simpa only [G,Z,Function.comp_def,Pi.sub_apply,coupledEuler,ite_eq_right hN.ne'] using hh
  have hGint : (∫ ω, G ω ∂μ)=
      (∫ z, V T (euler T N γ (fun t ↦ deriv (V t)) z N) ∂gaussianProduct (Fin (N+1)))-
        ∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)) := by
    have hh := hZlaw.integral_comp (hV.sub hE).aestronglyMeasurable
    simp only [Function.comp_def,Pi.sub_apply] at hh
    rw [integral_sub (hV.integrable (by norm_num)) (hE.integrable (by norm_num))] at hh
    simpa only [G,Z,Function.comp_def,Pi.sub_apply,coupledEuler,ite_eq_right hN.ne'] using hh
  have hbound : ∀ᵐ ω ∂μ, |F ω-G ω| ≤ (3/2 : ℝ)*stepSize T N*(γ T-γ 0) := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    have hS := h.feedback_state_error B hT hN ω hω
    have hE := h.feedback_energy_error B hT hN ω
    have hVl := (h.value_lipschitz ht).dist_le_mul
      (controlState B γ α 0 T ω) (coupledEuler T γ (fun t ↦ deriv (V t)) B N N ω)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hVl
    have hh := abs_sub_le (F ω-G ω)
      (V T (controlState B γ α 0 T ω)-V T (coupledEuler T γ (fun t ↦ deriv (V t)) B N N ω)) 0
    have hid : (F ω-G ω)-
      (V T (controlState B γ α 0 T ω)-V T (coupledEuler T γ (fun t ↦ deriv (V t)) B N N ω)) =
        -((1/2 : ℝ)*controlAccum γ α 2 T ω-valueMeshEnergy T N γ V N (Z ω)) := by
      dsimp [F,G]
      ring
    rw [hid,abs_neg,sub_zero,sub_zero] at hh
    linarith
  rw [←hGint,←integral_sub hFi hGi]
  have hh := abs_integral_le_integral_abs (μ := μ) (f := fun ω ↦ F ω-G ω)
  have hj := integral_mono_ae (hFi.sub hGi).abs
    (integrable_const ((3/2 : ℝ)*stepSize T N*(γ T-γ 0))) hbound
  have hc : (∫ _ : Ω, (3/2 : ℝ)*stepSize T N*(γ T-γ 0) ∂μ)=
      (3/2 : ℝ)*stepSize T N*(γ T-γ 0) := by simp
  exact hh.trans (hj.trans_eq hc)

lemma ValueStrip.feedback_payoff_tendsto
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) (hγM : Measurable γ) :
    Tendsto (fun N ↦ ∫ ω, V T (controlState B γ (feedbackControl B γ V T N) 0 T ω)-
      (1/2 : ℝ)*controlAccum γ (feedbackControl B γ V T N) 2 T ω ∂μ)
      atTop (𝓝 (V 0 0)) := by
  let p := fun N ↦ ∫ ω, V T (controlState B γ (feedbackControl B γ V T N) 0 T ω)-
      (1/2 : ℝ)*controlAccum γ (feedbackControl B γ V T N) 2 T ω ∂μ
  let q := fun N ↦ (∫ z, V T (euler T N γ (fun t ↦ deriv (V t)) z N)
      ∂gaussianProduct (Fin (N+1)))-
      ∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1))
  have hs : Tendsto (fun N : ℕ ↦ stepSize T N) atTop (𝓝 0) := by
    simpa only [stepSize,mul_zero,div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) :
        Tendsto (fun N : ℕ ↦ T*(N : ℝ)⁻¹) atTop (𝓝 (T*0)))
  have hpq : Tendsto (fun N ↦ p N-q N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦ (3/2 : ℝ)*stepSize T N*(γ T-γ 0))
    · filter_upwards [eventually_gt_atTop 0] with N hN
      simpa only [Real.norm_eq_abs,p,q] using h.feedback_payoff_approximation hB hBm hT hγM hN
    · simpa using (hs.const_mul (3/2 : ℝ)).mul_const (γ T-γ 0)
  have hq : Tendsto q atTop (𝓝 (V 0 0)) := by
    have hh := (value_mesh_expectation_error_tendsto hT hT1 h).add_const (V 0 0)
    convert hh using 1
    · ext N
      dsimp only [q]
      ring
    · simp
  have hh := hpq.add hq
  simpa only [sub_add_cancel,zero_add,p] using hh

theorem ValueStrip.progressive_control_value
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) (hγM : Measurable γ) :
    sSup {r | ∃ α : ℝ≥0 → Ω → ℝ,
      IsProgressive (Filtration.natural B hBm) α ∧ (∀ s ω, |α s ω|≤1) ∧
      r = ∫ ω, V T (controlState B γ α 0 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω ∂μ}
      = V 0 0 := by
  let S := {r | ∃ α : ℝ≥0 → Ω → ℝ,
      IsProgressive (Filtration.natural B hBm) α ∧ (∀ s ω, |α s ω|≤1) ∧
      r = ∫ ω, V T (controlState B γ α 0 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω ∂μ}
  have hb : ∀ r∈S, r≤V 0 0 := by
    rintro r ⟨α,hα,hαb,rfl⟩
    exact h.progressive_control_upper hB hBm hT hT1 hγM hα hαb 0
  have hp (N : ℕ) (hN : 0<N) :
      (∫ ω, V T (controlState B γ (feedbackControl B γ V T N) 0 T ω)-
        (1/2 : ℝ)*controlAccum γ (feedbackControl B γ V T N) 2 T ω ∂μ)∈S :=
    ⟨_,h.feedback_progressive hBm hT hN,h.feedback_bound B hT.le N,rfl⟩
  apply le_antisymm
  · exact csSup_le ⟨_,hp 1 (by norm_num)⟩ hb
  · apply le_of_tendsto (h.feedback_payoff_tendsto hB hBm hT hT1 hγM)
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact le_csSup ⟨V 0 0,hb⟩ (hp N hN)

end SKValue

end

end OAI
