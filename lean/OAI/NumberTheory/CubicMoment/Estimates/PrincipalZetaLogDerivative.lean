import OAI.NumberTheory.CubicMoment.Estimates.PrincipalZetaPole
import OAI.NumberTheory.CubicMoment.Estimates.AnalyticLocalLogDerivative

namespace OAI

/-! The pole contribution to the logarithmic derivative of the actual
principal ideal zeta function, with a bounded analytic remainder. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma principalIdealZeta_logDeriv_near_one :
    logDeriv principalIdealZeta =ᶠ[𝓝[≠] (1:ℂ)] fun s =>
      logDeriv principalZetaRegularFactor s-1/(s-1) := by
  have heq : principalIdealZeta =ᶠ[𝓝[≠] (1:ℂ)] fun s =>
      principalZetaRegularFactor s/(s-1) := by
    filter_upwards [(eventually_ne_nhds (one_ne_zero : (1:ℂ) ≠ 0)).filter_mono
      (nhdsWithin_le_nhds : 𝓝[≠] (1:ℂ) ≤ 𝓝 1),self_mem_nhdsWithin] with s hs hs1
    rw [principalZetaRegularFactor_eq hs hs1]
    exact (mul_div_cancel_left₀ (principalIdealZeta s) (sub_ne_zero.mpr hs1)).symm
  have hd := principalZetaRegularFactor_analyticAt_one.eventually_analyticAt.filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] (1:ℂ) ≤ 𝓝 1)
  have hn := (principalZetaRegularFactor_analyticAt_one.continuousAt.eventually
    (eventually_ne_nhds principalZetaRegularFactor_one_ne_zero)).filter_mono
      (nhdsWithin_le_nhds : 𝓝[≠] (1:ℂ) ≤ 𝓝 1)
  filter_upwards [logDeriv_congr_nhdsNE heq,hd,hn,self_mem_nhdsWithin]
    with s he hd hn hs
  rw [he,logDeriv_fun_div (f := principalZetaRegularFactor) (g := fun s : ℂ => s-1)
    s hn (sub_ne_zero.mpr hs) hd.differentiableAt (by fun_prop)]
  simp only [logDeriv_apply,deriv_sub_const,deriv_id'']

theorem principalIdealZeta_logDeriv_pole_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ s in 𝓝[≠] (1:ℂ),
      ‖logDeriv principalIdealZeta s+1/(s-1)‖ ≤ C := by
  let C : ℝ := ‖logDeriv principalZetaRegularFactor 1‖+1
  have hcont : ContinuousAt (logDeriv principalZetaRegularFactor) 1 := by
    exact principalZetaRegularFactor_analyticAt_one.deriv.continuousAt.div
      principalZetaRegularFactor_analyticAt_one.continuousAt
      principalZetaRegularFactor_one_ne_zero
  have hb : ∀ᶠ s in 𝓝 (1:ℂ), ‖logDeriv principalZetaRegularFactor s‖ < C :=
    hcont.norm.eventually (eventually_lt_nhds (by dsimp [C]; linarith))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [principalIdealZeta_logDeriv_near_one,
    hb.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (1:ℂ) ≤ 𝓝 1)] with s he hb
  rw [he,sub_add_cancel]
  exact hb.le

theorem principalIdealZeta_real_logDeriv_bound :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1+δ →
      (-logDeriv principalIdealZeta (σ:ℂ)).re ≤ 1/(σ-1)+C := by
  obtain ⟨C,hC,hb⟩ := principalIdealZeta_logDeriv_pole_bound
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhdsWithin_iff.mp hb
  refine ⟨C,δ,hC,hδ,?_⟩
  intro σ hσ hσδ
  have hmem : (σ:ℂ) ∈ Metric.ball (1:ℂ) δ ∩ {(1:ℂ)}ᶜ := by
    constructor
    · simp only [Metric.mem_ball,dist_eq_norm]
      have he : (σ:ℂ)-1=((σ-1:ℝ):ℂ) := by push_cast; rfl
      rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hσ)]
      linarith
    · simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
      exact_mod_cast hσ.ne'
  have he := (Complex.abs_re_le_norm _).trans (hδb hmem)
  have hr : (logDeriv principalIdealZeta (σ:ℂ)+1/((σ:ℂ)-1)).re=
      (logDeriv principalIdealZeta (σ:ℂ)).re+1/(σ-1) := by
    have hp : ((1/(σ-1):ℝ):ℂ)=1/((σ:ℂ)-1) := by push_cast; rfl
    rw [Complex.add_re,←hp,Complex.ofReal_re]
  rw [hr] at he
  simp only [Complex.neg_re]
  linarith [(abs_le.mp he).1]

end CubicFirstMoment

end

end OAI
