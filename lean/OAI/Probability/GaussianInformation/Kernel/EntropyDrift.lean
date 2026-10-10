import Mathlib
import OAI.Probability.GaussianInformation.Kernel.NoiseLaw

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential.DriftTools

lemma compensated_log_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f q c : α → ℝ)
    (hf : ∀ᵐ x ∂μ, 0 < f x) (hq : ∀ᵐ x ∂μ, 0 < q x)
    (hc : ∀ᵐ x ∂μ, 0 ≤ c x)
    (hu : AEStronglyMeasurable (fun x => q x*f x/(1+c x)) μ)
    (hmass : (∫⁻ x, ENNReal.ofReal (q x*f x/(1+c x)) ∂μ) ≤ 1)
    (hflog : Integrable (fun x => Real.log (f x)) μ)
    (hqlog : Integrable (fun x => Real.log (q x)) μ)
    (hclog : Integrable (fun x => Real.log (1+c x)) μ) :
    (∫ x,Real.log (f x) ∂μ) ≤
      (∫ x,Real.log (1+c x) ∂μ) - ∫ x,Real.log (q x) ∂μ := by
  have hu0 : ∀ᵐ x ∂μ, 0 ≤ q x*f x/(1+c x) := by
    filter_upwards [hf,hq,hc] with x hfx hqx hcx
    positivity
  have hui : Integrable (fun x => q x*f x/(1+c x)) μ :=
    ⟨hu,(hasFiniteIntegral_iff_ofReal hu0).mpr (hmass.trans_lt (by norm_num))⟩
  have huint : (∫ x,q x*f x/(1+c x) ∂μ) ≤ 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hui hu0] at hmass
    exact (ENNReal.ofReal_le_one).mp hmass
  have hpoint : ∀ᵐ x ∂μ, Real.log (f x) ≤
      q x*f x/(1+c x)-1+Real.log (1+c x)-Real.log (q x) := by
    filter_upwards [hf,hq,hc] with x hfx hqx hcx
    have hcp : 0 < 1+c x := by linarith
    have h := Real.log_le_sub_one_of_pos (div_pos (mul_pos hqx hfx) hcp)
    rw [Real.log_div (mul_ne_zero hqx.ne' hfx.ne') hcp.ne',Real.log_mul hqx.ne' hfx.ne'] at h
    linarith
  have hbound := integral_mono_ae hflog (((hui.sub (integrable_const 1)).add hclog).sub hqlog) hpoint
  simp only [Pi.sub_apply,Pi.add_apply] at hbound
  have he : (∫ x,q x*f x/(1+c x)-1+Real.log (1+c x)-Real.log (q x) ∂μ) =
      (∫ x,q x*f x/(1+c x) ∂μ)-1+(∫ x,Real.log (1+c x) ∂μ)-(∫ x,Real.log (q x) ∂μ) := by
    rw [integral_sub (f := fun x => q x*f x/(1+c x)-1+Real.log (1+c x))
      (g := fun x => Real.log (q x)) ((hui.sub (integrable_const 1)).add hclog) hqlog,
      integral_add (f := fun x => q x*f x/(1+c x)-1) (g := fun x => Real.log (1+c x))
        (hui.sub (integrable_const 1)) hclog,
      integral_sub (f := fun x => q x*f x/(1+c x)) (g := fun _ => (1:ℝ)) hui (integrable_const 1)]
    simp
  rw [he] at hbound
  linarith

lemma compensation_lintegral {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] (ν : Measure α) (Λ : Measure β)
    (K : β → α → ℝ≥0∞) (hxK : ∀ z, Measurable (K z))
    (κ : β → ι → ℝ≥0∞) (hκ : ∀ z, ∑ w,κ z w=1)
    (x : ι → α → ℝ≥0∞) (hx : ∀ w, Measurable (x w))
    (q : β → ℝ≥0∞) (hq : ∫⁻ z,q z ∂Λ=1) :
    (∫⁻ z,∑ w, ∫⁻ s, K z s * κ z w * q z * x w s /
      (1+∫⁻ u,K z u*x w u ∂ν) ∂ν ∂Λ) ≤ 1 := by
  calc
    _ ≤ ∫⁻ z,q z ∂Λ := by
      apply lintegral_mono
      intro z
      calc
        _ = ∑ w,κ z w*q z*((∫⁻ s,K z s*x w s ∂ν)/(1+∫⁻ u,K z u*x w u ∂ν)) := by
          apply Finset.sum_congr rfl
          intro w _
          let C := ∫⁻ u,K z u*x w u ∂ν
          calc
            _ = ∫⁻ s, (κ z w*q z/(1+C))*(K z s*x w s) ∂ν := by
              apply lintegral_congr; intro s; dsimp [C]; simp only [div_eq_mul_inv]; ring
            _ = (κ z w*q z/(1+C))*C :=
              lintegral_const_mul _ ((hxK z).mul (hx w))
            _ = _ := by dsimp [C]; simp only [div_eq_mul_inv]; ring
        _ ≤ ∑ w,κ z w*q z*1 := by
          apply Finset.sum_le_sum
          intro w _
          gcongr
          exact ENNReal.div_le_of_le_mul (by simp)
        _ = q z := by simp only [mul_one,← Finset.sum_mul,hκ z,one_mul]
    _ = 1 := hq

lemma log_young {u v a : ℝ} (hu : 0 ≤ u) (hv : 0 < v) (ha : 0 < a) :
    u*Real.log v ≤ u*Real.log u-u*Real.log a-u+a*v := by
  by_cases hu0 : u=0
  · simp only [hu0,zero_mul,sub_zero,zero_add]
    positivity
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have h := Real.log_le_sub_one_of_pos (div_pos (mul_pos ha hv) hup)
  rw [Real.log_div (mul_ne_zero ha.ne' hv.ne') hu0,Real.log_mul ha.ne' hv.ne'] at h
  have hh := mul_le_mul_of_nonneg_left h hu
  have hc : u*(a*v/u-1)=a*v-u := by field_simp
  rw [hc] at hh
  nlinarith

lemma weighted_log_moment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (u v : α → ℝ) (hu : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hv : ∀ᵐ x ∂μ, 0 < v x) (hui : Integrable u μ) (hvi : Integrable v μ)
    (huli : Integrable (fun x => u x*Real.log (u x)) μ)
    (huvi : Integrable (fun x => u x*Real.log (v x)) μ)
    {r G : ℝ} (hr : 0 < r) (hG : 0 < G)
    (hur : ∫ x,u x ∂μ=r) (hvG : (∫ x,v x ∂μ) ≤ G) :
    (∫ x,u x*Real.log (v x) ∂μ) ≤
      (∫ x,u x*Real.log (u x) ∂μ)-r*Real.log (r/G) := by
  have hpoint : ∀ᵐ x ∂μ,u x*Real.log (v x) ≤
      u x*Real.log (u x)-u x*Real.log (r/G)-u x+(r/G)*v x := by
    filter_upwards [hu,hv] with x hx hy
    exact log_young hx hy (div_pos hr hG)
  have hright : Integrable (fun x => u x*Real.log (u x)-u x*Real.log (r/G)-u x+(r/G)*v x) μ :=
    ((huli.sub (hui.mul_const _)).sub hui).add (hvi.const_mul _)
  have h := integral_mono_ae huvi hright hpoint
  rw [integral_add (f := fun x => u x*Real.log (u x)-u x*Real.log (r/G)-u x)
      (g := fun x => (r/G)*v x) ((huli.sub (hui.mul_const _)).sub hui) (hvi.const_mul _),
    integral_sub (f := fun x => u x*Real.log (u x)-u x*Real.log (r/G)) (g := u)
      (huli.sub (hui.mul_const _)) hui,
    integral_sub (f := fun x => u x*Real.log (u x)) (g := fun x => u x*Real.log (r/G)) huli (hui.mul_const _),
    integral_mul_const,integral_const_mul,hur] at h
  have hb := mul_le_mul_of_nonneg_left hvG (div_nonneg hr.le hG.le)
  rw [div_mul_cancel₀ _ hG.ne'] at hb
  linarith

lemma integral_log_le_log_of_integral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (v : α → ℝ)
    (hv : ∀ᵐ x ∂μ,0 < v x) (hvi : Integrable v μ)
    (hvlog : Integrable (fun x => Real.log (v x)) μ)
    {a : ℝ} (ha : 0 < a) (hva : (∫ x,v x ∂μ) ≤ a) :
    (∫ x,Real.log (v x) ∂μ) ≤ Real.log a := by
  have hpoint : ∀ᵐ x ∂μ,Real.log (v x) ≤ v x/a-1+Real.log a := by
    filter_upwards [hv] with x hx
    have h := Real.log_le_sub_one_of_pos (div_pos hx ha)
    rw [Real.log_div hx.ne' ha.ne'] at h
    linarith
  have h := integral_mono_ae hvlog (((hvi.div_const a).sub (integrable_const 1)).add (integrable_const (Real.log a))) hpoint
  have he : (∫ x,v x/a-1+Real.log a ∂μ) = (∫ x,v x ∂μ)/a-1+Real.log a := by
    rw [integral_add (f := fun x => v x/a-1) (g := fun _ => Real.log a)
        ((hvi.div_const a).sub (integrable_const 1)) (integrable_const _),
      integral_sub (f := fun x => v x/a) (g := fun _ => (1:ℝ)) (hvi.div_const a) (integrable_const 1),
      integral_div]
    simp
  change (∫ x,Real.log (v x) ∂μ) ≤ (∫ x,v x/a-1+Real.log a ∂μ) at h
  rw [he] at h
  have hb : (∫ x,v x ∂μ)/a ≤ 1 := (div_le_one ha).mpr hva
  linarith

lemma pow_one_add_le {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (1+x)^k ≤ 2^k*(1+x^k) := by
  have h : 1+x ≤ 2*max 1 x := by have := le_max_left (1:ℝ) x; have := le_max_right (1:ℝ) x; linarith
  calc
    _ ≤ (2*max 1 x)^k := pow_le_pow_left₀ (by positivity) h k
    _ = 2^k*(max 1 x)^k := mul_pow _ _ _
    _ ≤ 2^k*(1+x^k) := by
      gcongr
      rcases le_total x 1 with hh|hh
      · rw [max_eq_left hh,one_pow]; have := pow_nonneg hx k; linarith
      · rw [max_eq_right hh]; linarith

lemma integrable_of_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : AEStronglyMeasurable f μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf hC

lemma integral_weighted_log_moment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (u g : α → ℝ)
    (hu : Measurable u) (hg : Measurable g)
    (hu0 : ∀ x,0 ≤ u x) (hu1 : ∀ x,u x ≤ 1)
    (hg0 : ∀ x,0 ≤ g x) {M G : ℝ} (hgM : ∀ x,g x ≤ M) (hG : 0 ≤ G)
    (k : ℕ) (hk : 0 < k) (hmoment : (∫ x,(g x)^k ∂μ) ≤ G^k) :
    (∫ x,u x*Real.log (1+g x) ∂μ) ≤
      -(∫ x,u x ∂μ)*Real.log (∫ x,u x ∂μ)/(k:ℝ) +
        (∫ x,u x ∂μ)*Real.log (4*(1+G)) := by
  let r : ℝ := ∫ x,u x ∂μ
  have hui : Integrable u μ := integrable_of_bounded μ u hu.aestronglyMeasurable (C := 1)
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hu0 x)]; exact hu1 x))
  have hr : 0 ≤ r := integral_nonneg hu0
  have hgMi : Integrable (fun x => (g x)^k) μ :=
    integrable_of_bounded μ _ (hg.pow_const k).aestronglyMeasurable (C := M^k)
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hg0 x) k)]; exact pow_le_pow_left₀ (hg0 x) (hgM x) k))
  have hv0 (x : α) : 0 < (1+g x)^k := pow_pos (by linarith [hg0 x]) _
  have hvi : Integrable (fun x => (1+g x)^k) μ :=
    integrable_of_bounded μ _ ((measurable_const.add hg).pow_const k).aestronglyMeasurable (C := (1+M)^k)
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_pos (hv0 x)]; exact pow_le_pow_left₀ (by linarith [hg0 x]) (by linarith [hgM x]) k))
  have hlogi : Integrable (fun x => Real.log (1+g x)) μ :=
    integrable_of_bounded μ _ (measurable_const.add hg).log.aestronglyMeasurable (C := Real.log (1+M))
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith [hg0 x]))]
        exact Real.log_le_log (by linarith [hg0 x]) (by linarith [hgM x])))
  have huli : Integrable (fun x => u x*Real.log (u x)) μ := by
    obtain ⟨C,hC⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := 1)).image Real.continuous_mul_log).isBounded.exists_norm_le
    exact integrable_of_bounded μ _ (Real.continuous_mul_log.measurable.comp hu).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => hC _ (mem_image_of_mem _ ⟨hu0 x,hu1 x⟩)))
  have huli0 : (∫ x,u x*Real.log (u x) ∂μ) ≤ 0 := integral_nonpos (fun x =>
    mul_nonpos_of_nonneg_of_nonpos (hu0 x) (Real.log_nonpos (hu0 x) (hu1 x)))
  have huwlog : Integrable (fun x => u x*Real.log (1+g x)) μ :=
    hlogi.bdd_mul hu.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hu0 x)]; exact hu1 x))
  have huvi : Integrable (fun x => u x*Real.log ((1+g x)^k)) μ := by
    simp_rw [Real.log_pow]
    convert huwlog.const_mul (k:ℝ) using 1
    ext x
    ring
  by_cases hr0 : r=0
  · have huae : u =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hu0) hui).mp hr0
    have hz : (∫ x,u x*Real.log (1+g x) ∂μ)=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [huae] with x hx
      simp [hx]
    change _ ≤ -r*Real.log r/(k:ℝ)+r*Real.log (4*(1+G))
    rw [hz,hr0]; simp
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hvG : (∫ x,(1+g x)^k ∂μ) ≤ (4*(1+G))^k := by
    calc
      _ ≤ ∫ x,2^k*(1+(g x)^k) ∂μ := integral_mono hvi
        (((integrable_const 1).add hgMi).const_mul _) (fun x => pow_one_add_le (hg0 x) k)
      _ = 2^k*(1+∫ x,(g x)^k ∂μ) := by rw [integral_const_mul,integral_add (integrable_const 1) hgMi]; simp
      _ ≤ 2^k*(1+G^k) := by gcongr
      _ ≤ 2^k*(2*(1+G)^k) := by gcongr; have h1 : (1:ℝ) ≤ (1+G)^k := one_le_pow₀ (by linarith); have h2 : G^k ≤ (1+G)^k := pow_le_pow_left₀ hG (by linarith) k; linarith
      _ ≤ 2^k*(2^k*(1+G)^k) := by gcongr; exact le_self_pow₀ (by norm_num) (by omega)
      _ = _ := by rw [mul_pow,show (4:ℝ)=2*2 by norm_num,mul_pow]; ring
  have h := weighted_log_moment μ u (fun x => (1+g x)^k)
    (Filter.Eventually.of_forall hu0) (Filter.Eventually.of_forall hv0) hui hvi huli huvi hrp
    (by positivity : 0 < (4*(1+G))^k) rfl hvG
  have he : (∫ x,u x*Real.log ((1+g x)^k) ∂μ) = (k:ℝ)*(∫ x,u x*Real.log (1+g x) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Real.log_pow]; ring
  rw [he, Real.log_div hrp.ne' (by positivity), Real.log_pow] at h
  change _ ≤ -r*Real.log r/(k:ℝ)+r*Real.log (4*(1+G))
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  apply (mul_le_mul_iff_right₀ hkR).mp
  have heq : (k:ℝ)*(-r*Real.log r/(k:ℝ)+r*Real.log (4*(1+G))) =
      -r*Real.log r+r*((k:ℝ)*Real.log (4*(1+G))) := by field_simp
  rw [heq]
  nlinarith

end KernelPotential.DriftTools

end OAI
