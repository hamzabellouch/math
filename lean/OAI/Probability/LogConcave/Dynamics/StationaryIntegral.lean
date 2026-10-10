import Mathlib
import OAI.Probability.LogConcave.Dynamics.TriangularEquiv
import OAI.Probability.LogConcave.Sampling.MeasureSmoothLipschitz

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter MeasureTheory
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stationary_integral {f : E → E} (hf : ContDiff ℝ 1 f)
    {K : ℝ≥0} (hL : LipschitzWith K f) {μ : Measure E} [IsFiniteMeasure μ]
    (hfi : Integrable (fun x => ‖f x‖) μ)
    (hflux : ∀ψ : E → ℝ,ContDiff ℝ 1 ψ →
      (∃L : ℝ≥0,LipschitzWith L ψ) → (∃B : ℝ,∀x,‖ψ x‖≤B) →
      (∫x,(fderiv ℝ ψ x) (f x) ∂μ)=0)
    {a b : ℝ} (hab : a<b) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    {L : ℝ≥0} (hφL : LipschitzWith L φ) {B : ℝ} (hφB : ∀x,‖φ x‖≤B) :
    (∫y,φ (flow (fun _ _ => hL) (hf.continuous.comp continuous_snd)
      ⟨a,le_rfl,hab.le⟩ y b) ∂μ)=∫y,φ y ∂μ := by
  let hc : Continuous (uncurry (fun (_ : ℝ) => f)) := hf.continuous.comp continuous_snd
  let hD : Continuous (uncurry (fun (_ : ℝ) => fderiv ℝ f)) :=
    (hf.continuous_fderiv (by norm_num)).comp continuous_snd
  let hd : ∀ (_ : ℝ) (z : E),HasFDerivAt f (fderiv ℝ f z) z :=
    fun _ z => (hf.differentiable (by norm_num) z).hasFDerivAt
  let T : Icc a b := ⟨b,hab.le,le_rfl⟩
  let ψ := backwardTest hab.le hc (fun _ _ => hL) T φ
  let S := fun t => fderiv ℝ (fun y => ψ (t,y))
  let C : ℝ := (L:ℝ)*Real.exp ((K:ℝ)*(b-a))
  have hC : 0≤C := by dsimp [C]; positivity
  have hψ : Continuous ψ := backwardTest_continuous hab.le hc (fun _ _ => hL) T hφ.continuous
  have hψc (t : ℝ) : ContDiff ℝ 1 (fun y => ψ (t,y)) := by
    have he : (fun y => ψ (t,y))=φ ∘ (fun y =>
        flow (fun _ _ => hL) hc (projIcc a b hab.le t) y T) := by
      funext y
      exact backwardTest_eq hab.le hc (fun _ _ => hL) T φ (t,y)
    rw [he]
    exact hφ.comp (flow_contDiff_one hab.le hc (fun _ _ => hL) hD hd _ T)
  have hψL (t : ℝ) := backwardTest_lipschitz hab.le hc (fun _ _ => hL) T hφL t
  have hψB (t : ℝ) (y : E) : ‖ψ (t,y)‖≤B := hφB _
  have hSb (t : ℝ) (y : E) : ‖S t y‖≤C := norm_fderiv_le_of_lipschitz ℝ (hψL t)
  have him (t : ℝ) : Integrable (fun y => ψ (t,y)) μ :=
    (integrable_const B).mono' (hψ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall (hψB t))
  have hdm (t : ℝ) : Measurable (fun y => -(S t y (f y))) :=
    ((continuous_fst.clm_apply continuous_snd).measurable.comp
      ((measurable_fderiv ℝ (fun y => ψ (t,y))).prodMk hf.continuous.measurable)).neg
  have hdb (t : ℝ) (y : E) : ‖-(S t y (f y))‖≤C*‖f y‖ := by
    rw [norm_neg]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hSb t y) (norm_nonneg _))
  have hpd (t : ℝ) (ht : t∈Ioo a b) (y : E) :
      HasDerivAt (fun t => ψ (t,y)) (-(S t y (f y))) t := by
    have hh := backwardTest_chain hab.le hc (fun _ _ => hL) hD hd T
      (hφ.differentiable (by norm_num)) ht (hasDerivAt_const t y)
    simpa only [zero_sub,map_neg] using hh
  have hQd (t : ℝ) (ht : t∈Ioo a b) : HasDerivAt (fun t => ∫y,ψ (t,y) ∂μ) 0 t := by
    have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F:=fun t y => ψ (t,y)) (F':=fun t y => -(S t y (f y)))
      (Ioo_mem_nhds ht.1 ht.2)
      (Eventually.of_forall fun _ =>
        (hψ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (him t) (hdm t).aestronglyMeasurable
      (Eventually.of_forall fun y s _ => hdb s y) (hfi.const_mul C)
      (Eventually.of_forall fun y s hs => hpd s hs y)
    have hz := hflux (fun y => ψ (t,y)) (hψc t) ⟨_,hψL t⟩ ⟨B,hψB t⟩
    have he : (∫y,-(S t y (f y)) ∂μ)=0 := by rw [integral_neg]; exact neg_eq_zero.mpr hz
    rw [he] at hh
    exact hh.2
  have hQc : Continuous (fun t => ∫y,ψ (t,y) ∂μ) :=
    continuous_of_dominated
      (fun t => (hψ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (fun t => Eventually.of_forall (hψB t)) (integrable_const B)
      (Eventually.of_forall fun y => hψ.comp (continuous_id.prodMk continuous_const))
  obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope (fun t => ∫y,ψ (t,y) ∂μ) hab hQc.continuousOn
    (fun t ht => (hQd t ht).differentiableAt.differentiableWithinAt)
  rw [(hQd t ht).deriv] at he
  have heq : (∫y,ψ (b,y) ∂μ)=(∫y,ψ (a,y) ∂μ) :=
    sub_eq_zero.mp ((div_eq_zero_iff).mp he.symm |>.resolve_right (sub_ne_zero.mpr hab.ne'))
  have ha : (fun y => ψ (a,y))=(fun y => φ (flow (fun _ _ => hL) hc ⟨a,le_rfl,hab.le⟩ y b)) := by
    funext y
    dsimp [ψ]
    rw [backwardTest_eq,projIcc_of_mem _ (show a∈Icc a b from ⟨le_rfl,hab.le⟩)]
  have hb : (fun y => ψ (b,y))=φ := by
    funext y
    dsimp [ψ]
    rw [backwardTest_eq,projIcc_of_mem _ (show b∈Icc a b from ⟨hab.le,le_rfl⟩)]
    exact congrArg φ (flow_initial (fun _ _ => hL) hc T y)
  rw [ha,hb] at heq
  exact heq.symm

theorem stationary_law {f : E → E} (hf : ContDiff ℝ 1 f)
    {K : ℝ≥0} (hL : LipschitzWith K f) {μ : Measure E} [IsFiniteMeasure μ]
    (hfi : Integrable (fun x => ‖f x‖) μ)
    (hflux : ∀ψ : E → ℝ,ContDiff ℝ 1 ψ →
      (∃L : ℝ≥0,LipschitzWith L ψ) → (∃B : ℝ,∀x,‖ψ x‖≤B) →
      (∫x,(fderiv ℝ ψ x) (f x) ∂μ)=0)
    {a b : ℝ} (hab : a<b) :
    μ.map (fun y => flow (fun _ _ => hL) (hf.continuous.comp continuous_snd)
      ⟨a,le_rfl,hab.le⟩ y b)=μ := by
  apply measure_eq_of_smooth_lipschitz
  intro φ hφ hφL hφB
  obtain ⟨L,hφL⟩ := hφL
  obtain ⟨B,hφB⟩ := hφB
  rw [integral_map (flow_lipschitz (fun _ _ => hL) (hf.continuous.comp continuous_snd)
    ⟨a,le_rfl,hab.le⟩ ⟨b,hab.le,le_rfl⟩).continuous.aemeasurable hφ.continuous.aestronglyMeasurable]
  exact stationary_integral hf hL hfi hflux hab hφ hφL hφB
end LogConcaveSampling.GlobalODE

end

end

end

end OAI
