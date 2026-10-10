import Mathlib
import OAI.Probability.SKValue.Evolution.HeatContinuity
import OAI.Probability.SKValue.Equations.JetAlgebra

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma heat_jet_continuous {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ∀ n, ExpGrowth (iteratedDeriv n f)) (j : ℕ) :
    Continuous (fun p : ℝ×ℝ ↦ iteratedDeriv j (heat p.1 f) p.2) := by
  simp_rw [heat_iteratedDeriv hf hg]
  exact heat_continuous (smooth_iteratedDeriv hf j).continuous (hg j)

lemma heat_jet_time {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ∀ n, ExpGrowth (iteratedDeriv n f)) (j : ℕ) (x : ℝ) {h : ℝ} (hh : 0<h) :
    HasDerivAt (fun r ↦ iteratedDeriv j (heat r f) x)
      ((1/2 : ℝ)*iteratedDeriv (j+2) (heat h f) x) h := by
  simp_rw [heat_iteratedDeriv hf hg]
  apply heat_time_hasDerivAt (f' := iteratedDeriv (j+1) f)
  · intro y
    simpa only [iteratedDeriv_succ] using
      ((hf.differentiable_iteratedDeriv j (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)) y).hasDerivAt
  · intro y
    simpa only [show j+2=(j+1)+1 from rfl,iteratedDeriv_succ] using
      ((hf.differentiable_iteratedDeriv (j+1) (ENat.natCast_lt_of_coe_top_le_withTop le_rfl (j+1))) y).hasDerivAt
  · exact (smooth_iteratedDeriv hf (j+2)).continuous
  · exact hg j
  · exact hg (j+1)
  · exact hg (j+2)
  · exact hh

lemma heat_normalizedJet_continuous {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ∀ n, ExpGrowth (iteratedDeriv n f))
    (hp : ∀ h x, heat h f x≠0) (j : ℕ) :
    Continuous (fun p : ℝ×ℝ ↦ normalizedJet (fun r ↦ heat r f) j p.1 p.2) := by
  exact (heat_jet_continuous hf hg j).div
    (heat_continuous hf.continuous (by simpa only [iteratedDeriv_zero] using hg 0)) (fun p ↦ hp p.1 p.2)

lemma heat_normalizedJet_time {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ∀ n, ExpGrowth (iteratedDeriv n f))
    (hp : ∀ h x, heat h f x≠0) (j : ℕ) (x : ℝ) {h : ℝ} (hh : 0<h) :
    HasDerivAt (fun r ↦ normalizedJet (fun s ↦ heat s f) j r x)
      ((1/2 : ℝ)*(normalizedJet (fun s ↦ heat s f) (j+2) h x-
        normalizedJet (fun s ↦ heat s f) j h x*normalizedJet (fun s ↦ heat s f) 2 h x)) h := by
  have hd := (heat_jet_time hf hg j x hh).div (heat_jet_time hf hg 0 x hh) (hp h x)
  convert! hd using 1
  dsimp only [normalizedJet]
  simp only [iteratedDeriv_zero,zero_add]
  field_simp [hp h x]

lemma nonneg_time_lipschitz {f g : ℝ → ℝ} {C : ℝ} (hC : 0≤C)
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ h, 0<h → HasDerivAt f (g h) h)
    (hb : ∀ h, 0≤h → |g h|≤C) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |f s-f t|≤C* |s-t| := by
  wlog hst : s≤t generalizing s t
  · simpa only [abs_sub_comm] using this ht hs (le_of_not_ge hst)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hf.continuousOn
    (fun r hr ↦ hd r (hs.trans_lt hr.1)) (hg.intervalIntegrable _ _)
  have hb' := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (f := g) (C := |C|) (fun r hr ↦ by
      rw [uIoc_of_le hst] at hr
      simpa only [Real.norm_eq_abs] using
        (hb r (hs.trans hr.1.le)).trans (le_abs_self C))
  rw [he,Real.norm_eq_abs] at hb'
  simpa only [abs_of_nonneg hC,abs_sub_comm,mul_comm] using hb'

lemma coleHopf_gradient_jet_expr {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0<c) (n : ℕ) (h : ℝ) :
    iteratedDeriv n (deriv (coleHopf c h ψ)) = fun x ↦ c⁻¹*
      JetExpr.eval (fun j ↦ normalizedJet (fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))) j h x)
        (JetExpr.logGradientJet n) := by
  let F := fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))
  have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
  have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
  have hs : ∀ r, ContDiff ℝ ∞ (F r) := fun r ↦ heat_contDiff hes hg r
  have hp : ∀ r x, F r x≠0 := fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
  rw [coleHopf_deriv_eq_normalizedJet hψ.lipschitz hψ.smooth hψ.jets hc h]
  funext x
  rw [iteratedDeriv_const_mul_field,
    JetExpr.iteratedDeriv_logGradientJet
      (fun j ↦ normalizedJet_smooth hs hp j h) (fun j ↦ normalizedJet_deriv hs hp j h)]

lemma SmoothTerminal.coleHopf_joint_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0≤c) (n : ℕ) :
    Continuous (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (coleHopf c p.1 ψ)) p.2) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp_rw [coleHopf_zero_coeff,←iteratedDeriv_succ']
    exact heat_jet_continuous hψ.smooth hψ.growth (n+1)
  · have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
    have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
    have hp : ∀ r x, heat r (fun y ↦ Real.exp (c*ψ y)) x≠0 :=
      fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
    simp_rw [coleHopf_gradient_jet_expr hψ hc]
    exact continuous_const.mul (JetExpr.continuous_eval (fun j ↦ heat_normalizedJet_continuous hes hg hp j) _)

lemma SmoothTerminal.coleHopf_time_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0≤c) (n : ℕ) :
    ∃ d : ℝ → ℝ → ℝ, Continuous (fun p : ℝ×ℝ ↦ d p.1 p.2) ∧
      (∃ C : ℝ, 0≤C ∧ ∀ h x, |d h x|≤C) ∧
      ∀ h x, 0<h → HasDerivAt (fun r ↦ iteratedDeriv n (deriv (coleHopf c r ψ)) x) (d h x) h := by
  rcases hc.eq_or_lt with rfl | hc
  · let d := fun h x ↦ (1/2 : ℝ)*iteratedDeriv (n+3) (heat h ψ) x
    refine ⟨d,continuous_const.mul (heat_jet_continuous hψ.smooth hψ.growth _),?_,?_⟩
    · obtain ⟨C,hC,hb⟩ := hψ.jets.bound (n+2)
      refine ⟨C/2,by positivity,?_⟩
      intro h x
      dsimp only [d]
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2),
        heat_iteratedDeriv hψ.smooth hψ.growth,show n+3=(n+2)+1 from rfl,iteratedDeriv_succ']
      linarith [heat_bound hC hb h x]
    · intro h x hh
      simpa only [coleHopf_zero_coeff,←iteratedDeriv_succ'] using heat_jet_time hψ.smooth hψ.growth (n+1) x hh
  · let F := fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))
    let R := fun j (p : ℝ×ℝ) ↦ normalizedJet F j p.1 p.2
    let E := JetExpr.D JetExpr.σh (JetExpr.logGradientJet n)
    let d := fun h x ↦ c⁻¹*JetExpr.eval (fun j ↦ R j (h,x)) E
    have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
    have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
    have hp : ∀ r x, F r x≠0 := fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
    have hR : ∀ j, Continuous (R j) := fun j ↦ heat_normalizedJet_continuous hes hg hp j
    refine ⟨d,continuous_const.mul (JetExpr.continuous_eval hR E),?_,?_⟩
    · have hRb : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ p, |R j p|≤C := by
        intro j
        obtain ⟨C,hC,hb⟩ := exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc.le j
        exact ⟨C,hC,fun p ↦ hb p.1 p.2⟩
      obtain ⟨C,hC,hb⟩ := JetExpr.uniform_bound hRb E
      refine ⟨|c⁻¹| * C,by positivity,?_⟩
      intro h x
      dsimp only [d]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb (h,x)) (abs_nonneg _)
    · intro h x hh
      simp_rw [coleHopf_gradient_jet_expr hψ hc]
      apply HasDerivAt.const_mul
      apply JetExpr.hasDerivAt_eval
      intro j
      simpa only [JetExpr.eval_σh] using heat_normalizedJet_time hes hg hp j x hh

lemma SmoothTerminal.coleHopf_jets_time_lipschitz {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0≤c) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s t x, 0 ≤ s → 0 ≤ t →
      |iteratedDeriv n (deriv (coleHopf c s ψ)) x-iteratedDeriv n (deriv (coleHopf c t ψ)) x|≤C* |s-t| := by
  obtain ⟨d,hdc,⟨C,hC,hb⟩,hd⟩ := hψ.coleHopf_time_jets hc n
  refine ⟨C,hC,?_⟩
  intro s t x hs ht
  exact nonneg_time_lipschitz hC
    ((hψ.coleHopf_joint_jets hc n).comp (continuous_id.prodMk continuous_const))
    (hdc.comp (continuous_id.prodMk continuous_const))
    (fun h hh ↦ hd h x hh) (fun h _ ↦ hb h x) hs ht

end SKValue

end

end OAI
