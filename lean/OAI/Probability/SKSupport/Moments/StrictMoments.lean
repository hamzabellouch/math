import Mathlib
import OAI.Probability.SKSupport.Diffusion.Diffusion

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma integral_pos_of_interval_support {P : Measure Ω} {X : Ω → ℝ} {f : ℝ → ℝ}
    (hX : ∀ a b : ℝ, a < b → 0 < P {ξ | X ξ ∈ Ioo a b})
    (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) (hi : Integrable (fun ξ => f (X ξ)) P)
    (hne : ∃ x, f x ≠ 0) : 0 < ∫ ξ, f (X ξ) ∂P := by
  obtain ⟨x,hx⟩ := hne
  have he : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hf.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hx)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp he
  apply (integral_pos_iff_support_of_nonneg (fun ξ => hn (X ξ)) hi).mpr
  apply (hX (x-ε) (x+ε) (by linarith)).trans_le
  apply measure_mono
  intro ξ hξ
  change f (X ξ) ≠ 0
  apply hball
  rw [Real.dist_eq,abs_lt]
  change x-ε < X ξ ∧ X ξ < x+ε at hξ
  constructor <;> linarith [hξ.1,hξ.2]

lemma curvature_not_identically_zero (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : ∃ x, curvature W γ t x ≠ 0 := by
  by_contra hh
  push Not at hh
  have hV := value_contDiff W γ ht0 ht1
  have hG := (contDiff_infty_iff_deriv.mp hV).2
  have hg (x : ℝ) : gradient W γ t x=0 := by
    have hc := is_const_of_deriv_eq_zero (hG.differentiable (by simp)) hh x 0
    exact hc.trans (gradient_zero W γ ht0 ht1)
  have hv (x : ℝ) := is_const_of_deriv_eq_zero (hV.differentiable (by simp)) hg x 0
  have h := abs_le_value W γ t (value W γ t 0+1) ht1.le
  rw [hv (value W γ t 0+1)] at h
  have := le_abs_self (value W γ t 0+1)
  linarith

lemma third_not_identically_zero (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : ∃ x, deriv (curvature W γ t) x ≠ 0 := by
  by_contra hh
  push Not at hh
  have hV := value_contDiff W γ ht0 ht1
  have hG := (contDiff_infty_iff_deriv.mp hV).2
  have hC := (contDiff_infty_iff_deriv.mp hG).2
  have hc (x : ℝ) : curvature W γ t x=curvature W γ t 0 :=
    is_const_of_deriv_eq_zero (hC.differentiable (by simp)) hh x 0
  let c := curvature W γ t 0
  have ha (x : ℝ) : HasDerivAt (fun y => gradient W γ t y-c*y) 0 x := by
    have hd := (hG.differentiable (by simp) x).hasDerivAt
    change HasDerivAt (gradient W γ t) (curvature W γ t x) x at hd
    have hdc := hd.sub ((hasDerivAt_id x).const_mul c)
    have hz : curvature W γ t x-c=0 := by rw [hc];dsimp only [c];ring
    rw [mul_one,hz] at hdc
    exact hdc
  have he (x : ℝ) : gradient W γ t x=c*x := by
    have h := is_const_of_deriv_eq_zero (fun y => (ha y).differentiableAt) (fun y => (ha y).deriv) x 0
    rw [gradient_zero W γ ht0 ht1,mul_zero,sub_zero] at h
    linarith
  have hz : c=0 := by
    by_contra hc0
    have hb := gradient_abs_le_one W γ t (2/c) ht1.le
    rw [he,mul_div_cancel₀ _ hc0] at hb
    norm_num at hb
  obtain ⟨x,hx⟩ := curvature_not_identically_zero W γ ht0 ht1
  exact hx ((hc x).trans hz)

lemma actual_jet_even_moment_pos (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht0 : 0 < (t:ℝ)) (n k : ℕ) (hk : 0 < k)
    (hne : ∃ x, iteratedDeriv (n+1) (value W γ t) x ≠ 0) :
    0 < ∫ ξ, (iteratedDeriv (n+1) (value W γ t)
      (diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ))^(2*k) ∂W.law := by
  let := W.isProbability
  have hs := contDiff_iteratedDeriv_infty (value_contDiff W γ t.property.1 t.property.2) (n+1)
  have hm : Measurable (diffusion W γ (⟨t,t.property.1⟩:ℝ≥0)) := by
    let ℱ := Filtration.natural W.B (fun s => (W.measurable s).stronglyMeasurable)
    have ha : Measurable[ℱ (⟨t,t.property.1⟩:ℝ≥0)] (diffusion W γ (⟨t,t.property.1⟩:ℝ≥0)) :=
      (diffusion_progressive W γ).adapted (⟨t,t.property.1⟩:ℝ≥0)
    exact ha.mono (ℱ.le _) le_rfl
  obtain ⟨C,hC,hbound⟩ := value_uniform_derivative_bounds W γ t.property.1 t.property.2 n
  have hi : Integrable (fun ξ => (iteratedDeriv (n+1) (value W γ t)
      (diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ))^(2*k)) W.law := by
    apply Integrable.mono' (integrable_const (μ := W.law) (C^(2*k)))
    · exact ((hs.continuous.measurable.comp hm).pow_const _).aestronglyMeasurable
    · filter_upwards [] with ξ
      rw [Real.norm_eq_abs,abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbound t ⟨t.property.1,le_rfl⟩ _) _
  apply integral_pos_of_interval_support
    (P := W.law) (X := diffusion W γ (⟨t,t.property.1⟩:ℝ≥0))
    (f := fun x => (iteratedDeriv (n+1) (value W γ t) x)^(2*k))
    (fun a b hab => diffusion_interval_pos W γ t ht0 hab)
    (hs.continuous.pow _) (fun x => by rw [pow_mul];exact pow_nonneg (pow_two_nonneg _) k) hi
  obtain ⟨x,hx⟩ := hne
  exact ⟨x,(pow_ne_zero_iff (Nat.ne_of_gt (Nat.mul_pos (by decide) hk))).mpr hx⟩

end ZeroTemperatureSK

end
end

end OAI
