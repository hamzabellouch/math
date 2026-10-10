import Mathlib
import OAI.Probability.GaussianInformation.Kernel.EntropyDrift

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential.DriftTools
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

lemma fresh_weighted_log_moment {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : α → ℝ) (m : α × β → ℝ≥0∞)
    (hu : Measurable u) (hm : Measurable m)
    (hu0 : ∀ a,0 ≤ u a) (hu1 : ∀ a,u a ≤ 1)
    {B G c : ℝ} (hB : 0 ≤ B) (hG : 0 ≤ G) (hc : 0 ≤ c)
    (hmB : ∀ a b,m (a,b) ≤ ENNReal.ofReal B) (k : ℕ) (hk : 0 < k)
    (hmoment : (∫⁻ a,(∫⁻ b,m (a,b) ∂ν)^k ∂μ) ≤ ENNReal.ofReal G^k) :
    (∫ a,u a*(∫ b,Real.log (1+c*(m (a,b)).toReal) ∂ν) ∂μ) ≤
      -(∫ a,u a ∂μ)*Real.log (∫ a,u a ∂μ)/(k:ℝ)+
        (∫ a,u a ∂μ)*Real.log (4*(1+c*G)) := by
  let g : α → ℝ := fun a => (∫⁻ b,m (a,b) ∂ν).toReal
  have hgE : Measurable (fun a => ∫⁻ b,m (a,b) ∂ν) := Measurable.lintegral_prod_right hm
  have hg : Measurable g := hgE.ennreal_toReal
  have hmt (a : α) (b : β) : m (a,b) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmB a b)
  have hgBE (a : α) : (∫⁻ b,m (a,b) ∂ν) ≤ ENNReal.ofReal B := by
    calc
      _ ≤ ∫⁻ _b,ENNReal.ofReal B ∂ν := lintegral_mono (hmB a)
      _ = _ := by simp
  have hgt (a : α) : (∫⁻ b,m (a,b) ∂ν) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hgBE a)
  have hgB (a : α) : g a ≤ B := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hgBE a)).trans_eq (ENNReal.toReal_ofReal hB)
  have hmBr (a : α) (b : β) : (m (a,b)).toReal ≤ B :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmB a b)).trans_eq (ENNReal.toReal_ofReal hB)
  have hfi (a : α) : Integrable (fun b => (m (a,b)).toReal) ν :=
    integrable_of_bounded ν _ ((hm.comp (measurable_const.prodMk measurable_id)).ennreal_toReal.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun b => by rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]; exact hmBr a b))
  have hgeq (a : α) : (∫ b,(m (a,b)).toReal ∂ν)=g a :=
    integral_toReal (hm.comp (measurable_const.prodMk measurable_id)).aemeasurable
      (Filter.Eventually.of_forall (fun b => (hmt a b).lt_top))
  have hgmoment : (∫ a,(c*g a)^k ∂μ) ≤ (c*G)^k := by
    have he : (∫ a,(g a)^k ∂μ) = (∫⁻ a,(∫⁻ b,m (a,b) ∂ν)^k ∂μ).toReal := by
      dsimp only [g]
      simp_rw [← ENNReal.toReal_pow]
      exact integral_toReal (hgE.pow_const k).aemeasurable
        (Filter.Eventually.of_forall (fun a => (ENNReal.pow_ne_top (hgt a)).lt_top))
    have hb : (∫ a,(g a)^k ∂μ) ≤ G^k := by
      rw [he]
      have h := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hmoment
      simpa only [ENNReal.toReal_pow,ENNReal.toReal_ofReal hG] using h
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hb (pow_nonneg hc k)
  have hcg : Measurable (fun a => c*g a) := measurable_const.mul hg
  have hpoint (a : α) : (∫ b,Real.log (1+c*(m (a,b)).toReal) ∂ν) ≤ Real.log (1+c*g a) := by
    have hvpos (b : β) : 0 < 1+c*(m (a,b)).toReal := by positivity
    have hvlog : Integrable (fun b => Real.log (1+c*(m (a,b)).toReal)) ν := by
      apply integrable_of_bounded ν _
        ((measurable_const.add (measurable_const.mul
          (hm.comp (measurable_const.prodMk measurable_id)).ennreal_toReal)).log.aestronglyMeasurable)
        (C := Real.log (1+c*B))
      filter_upwards [] with b
      dsimp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, id_eq]
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith [mul_nonneg hc (ENNReal.toReal_nonneg (a := m (a,b))) ]))]
      exact Real.log_le_log (hvpos b) (by nlinarith [hmBr a b])
    apply integral_log_le_log_of_integral_le ν _
      (Filter.Eventually.of_forall hvpos) ((integrable_const 1).add ((hfi a).const_mul c))
      hvlog (by dsimp [g]; positivity)
    rw [integral_add (integrable_const 1) ((hfi a).const_mul c),integral_const_mul,hgeq]
    simp
  have hlogM : ∀ a b, ‖Real.log (1+c*(m (a,b)).toReal)‖ ≤ Real.log (1+c*B) := by
    intro a b
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith [mul_nonneg hc (ENNReal.toReal_nonneg (a := m (a,b))) ]))]
    exact Real.log_le_log (by positivity) (by nlinarith [hmBr a b])
  have hlogint : Integrable (fun t : α × β => Real.log (1+c*(m t).toReal)) (μ.prod ν) :=
    integrable_of_bounded _ _
      ((measurable_const.add (measurable_const.mul hm.ennreal_toReal)).log.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun t => hlogM t.1 t.2))
  have hlefti : Integrable (fun a => u a*(∫ b,Real.log (1+c*(m (a,b)).toReal) ∂ν)) μ :=
    hlogint.integral_prod_left.bdd_mul hu.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun a => by rw [Real.norm_eq_abs,abs_of_nonneg (hu0 a)]; exact hu1 a))
  have hrighti : Integrable (fun a => u a*Real.log (1+c*g a)) μ := by
    have hi : Integrable (fun a => Real.log (1+c*g a)) μ := by
      apply integrable_of_bounded μ _ (measurable_const.add hcg).log.aestronglyMeasurable
        (C := Real.log (1+c*B))
      filter_upwards [] with a
      have hg0 : 0 ≤ g a := ENNReal.toReal_nonneg
      dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith [mul_nonneg hc hg0]))]
      exact Real.log_le_log (by positivity) (by nlinarith [hgB a])
    exact hi.bdd_mul hu.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun a => by rw [Real.norm_eq_abs,abs_of_nonneg (hu0 a)]; exact hu1 a))
  calc
    _ ≤ ∫ a,u a*Real.log (1+c*g a) ∂μ := integral_mono hlefti hrighti
      (fun a => mul_le_mul_of_nonneg_left (hpoint a) (hu0 a))
    _ ≤ _ := integral_weighted_log_moment μ u (fun a => c*g a) hu hcg hu0 hu1
      (fun _ => mul_nonneg hc ENNReal.toReal_nonneg) (M := c*B)
      (fun a => mul_le_mul_of_nonneg_left (hgB a) hc) (mul_nonneg hc hG) k hk hgmoment

end KernelPotential.DriftTools

end OAI
