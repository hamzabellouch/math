import OAI.NumberTheory.CubicMoment.Estimates.HeckeZeros

namespace OAI

/-! The local principal part of a logarithmic derivative at a zero,
proved directly from analytic factorization. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma logDeriv_centered_power (ρ z : ℂ) (n : ℕ) :
    logDeriv (fun w : ℂ => (w-ρ)^n) z=(n:ℂ)/(z-ρ) := by
  rw [logDeriv_fun_pow (f := fun w : ℂ => w-ρ) (x := z) (by fun_prop) n]
  have h : logDeriv (fun w : ℂ => w-ρ) z=1/(z-ρ) := by
    simp only [logDeriv_apply,deriv_sub_const,deriv_id'']
  rw [h,mul_one_div]

lemma analytic_factor_logDeriv {L g : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hg : AnalyticAt ℂ g ρ) (hg0 : g ρ ≠ 0)
    (heq : L =ᶠ[𝓝 ρ] fun z => (z-ρ)^n*g z) :
    logDeriv L =ᶠ[𝓝[≠] ρ] fun z => (n:ℂ)/(z-ρ)+logDeriv g z := by
  have he : logDeriv L =ᶠ[𝓝[≠] ρ] logDeriv (fun z => (z-ρ)^n*g z) :=
    (logDeriv_congr_nhds heq).filter_mono nhdsWithin_le_nhds
  have hd : ∀ᶠ z in 𝓝[≠] ρ, AnalyticAt ℂ g z :=
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hn : ∀ᶠ z in 𝓝[≠] ρ, g z ≠ 0 :=
    (hg.continuousAt.eventually (eventually_ne_nhds hg0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [he,hd,hn,self_mem_nhdsWithin] with z he hd hn hz
  change z ≠ ρ at hz
  rw [he,logDeriv_fun_mul (f := fun w : ℂ => (w-ρ)^n) (g := g)
    z (pow_ne_zero _ (sub_ne_zero.mpr hz)) hn
    (by fun_prop) hd.differentiableAt,
    logDeriv_centered_power]

theorem entire_zero_logDeriv_principal_part {L : ℂ → ℂ}
    (hL : Differentiable ℂ L) {s : ℂ} (hs : L s ≠ 0)
    {ρ : ℂ} (hρ : L ρ=0) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      logDeriv L =ᶠ[𝓝[≠] ρ] fun z => (n:ℂ)/(z-ρ)+logDeriv g z := by
  obtain ⟨n,hn,g,hg,hg0,heq⟩ := entire_zero_local_factor hL hs hρ
  exact ⟨n,hn,g,hg,hg0,analytic_factor_logDeriv hg hg0 heq⟩

end CubicFirstMoment

end

end OAI
