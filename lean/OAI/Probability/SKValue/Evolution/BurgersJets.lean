import Mathlib
import OAI.Probability.SKValue.Evolution.LogHeatJets

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

noncomputable def scaledHeatJet (c : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  c*iteratedDeriv n (deriv (coleHopf c t ψ)) x

lemma scaledHeatJet_expr {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0<c) (n : ℕ) (t x : ℝ) : scaledHeatJet c ψ n t x=
    JetExpr.eval (fun j ↦ normalizedJet (fun h ↦ heat h (fun y ↦ Real.exp (c*ψ y))) j t x)
      (JetExpr.logGradientJet n) := by
  dsimp only [scaledHeatJet]
  rw [coleHopf_gradient_jet_expr hψ hc]
  simp only [←mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]

lemma scaledHeatJet_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0≤c) (n : ℕ) : Continuous (fun p : ℝ×ℝ ↦ scaledHeatJet c ψ n p.1 p.2) :=
  continuous_const.mul (hψ.coleHopf_joint_jets hc n)

lemma scaledHeatJet_bound {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0<c) (n : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ t x, |scaledHeatJet c ψ n t x|≤C := by
  obtain ⟨C,hC,hb⟩ := coleHopf_deriv_uniform_bounds_of_pos hψ.lipschitz hψ.smooth hψ.jets hc n
  refine ⟨c*C,mul_nonneg hc.le hC,?_⟩
  intro t x
  dsimp only [scaledHeatJet]
  rw [abs_mul,abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left (hb t x) hc.le

lemma scaledHeatJet_space {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0≤c) (n : ℕ) (t x : ℝ) :
    HasDerivAt (scaledHeatJet c ψ n t) (scaledHeatJet c ψ (n+1) t x) x := by
  have hs := (hψ.evolve hc t).jets.smooth
  have hd := (hs.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) x).hasDerivAt
  rw [←iteratedDeriv_succ] at hd
  exact hd.const_mul c

lemma scaledHeatJet_time_expr {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0<c) (n : ℕ) {t : ℝ} (ht : 0<t) (x : ℝ) :
    HasDerivAt (fun s ↦ scaledHeatJet c ψ n s x)
      (JetExpr.eval (fun j ↦ normalizedJet (fun h ↦ heat h (fun y ↦ Real.exp (c*ψ y))) j t x)
        (JetExpr.D JetExpr.σh (JetExpr.logGradientJet n))) t := by
  simp_rw [scaledHeatJet_expr hψ hc]
  have hes : ContDiff ℝ ∞ (fun y ↦ Real.exp (c*ψ y)) := (contDiff_const.mul hψ.smooth).exp
  have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
  have hp : ∀ h y, heat h (fun z ↦ Real.exp (c*ψ z)) y≠0 :=
    fun h y ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le y (Real.sqrt h)).ne'
  apply JetExpr.hasDerivAt_eval
  intro j
  simpa only [JetExpr.eval_σh] using heat_normalizedJet_time hes hg hp j x ht

namespace JetExpr
lemma burgers0 (R : ℕ → ℝ) : eval R (D σh (logGradientJet 0))=
    (1/2 : ℝ)*eval R (logGradientJet 2)+
      eval R (logGradientJet 0)*eval R (logGradientJet 1) := by
  simp only [logGradientJet,D,σh,σx,eval]
  norm_num
  ring

lemma burgers1 (R : ℕ → ℝ) : eval R (D σh (logGradientJet 1))=
    (1/2 : ℝ)*eval R (logGradientJet 3)+(eval R (logGradientJet 1))^2+
      eval R (logGradientJet 0)*eval R (logGradientJet 2) := by
  simp only [logGradientJet,D,σh,σx,eval]
  norm_num
  ring

lemma burgers2 (R : ℕ → ℝ) : eval R (D σh (logGradientJet 2))=
    (1/2 : ℝ)*eval R (logGradientJet 4)+
      3*eval R (logGradientJet 1)*eval R (logGradientJet 2)+
      eval R (logGradientJet 0)*eval R (logGradientJet 3) := by
  simp only [logGradientJet,D,σh,σx,eval]
  norm_num
  ring

lemma burgers3 (R : ℕ → ℝ) : eval R (D σh (logGradientJet 3))=
    (1/2 : ℝ)*eval R (logGradientJet 5)+
      3*(eval R (logGradientJet 2))^2+
      4*eval R (logGradientJet 1)*eval R (logGradientJet 3)+
      eval R (logGradientJet 0)*eval R (logGradientJet 4) := by
  simp only [logGradientJet,D,σh,σx,eval]
  norm_num
  ring
end JetExpr

lemma scaledHeatJet_time0 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0<c) {t : ℝ} (ht : 0<t) (x : ℝ) :
    HasDerivAt (fun s ↦ scaledHeatJet c ψ 0 s x)
      ((1/2 : ℝ)*scaledHeatJet c ψ 2 t x+
        scaledHeatJet c ψ 0 t x*scaledHeatJet c ψ 1 t x) t := by
  have hd := scaledHeatJet_time_expr hψ hc 0 ht x
  rw [JetExpr.burgers0] at hd
  simpa only [scaledHeatJet_expr hψ hc] using hd

lemma scaledHeatJet_time1 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0<c) {t : ℝ} (ht : 0<t) (x : ℝ) :
    HasDerivAt (fun s ↦ scaledHeatJet c ψ 1 s x)
      ((1/2 : ℝ)*scaledHeatJet c ψ 3 t x+(scaledHeatJet c ψ 1 t x)^2+
        scaledHeatJet c ψ 0 t x*scaledHeatJet c ψ 2 t x) t := by
  have hd := scaledHeatJet_time_expr hψ hc 1 ht x
  rw [JetExpr.burgers1] at hd
  simpa only [scaledHeatJet_expr hψ hc] using hd

lemma scaledHeatJet_time2 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0<c) {t : ℝ} (ht : 0<t) (x : ℝ) :
    HasDerivAt (fun s ↦ scaledHeatJet c ψ 2 s x)
      ((1/2 : ℝ)*scaledHeatJet c ψ 4 t x+
        3*scaledHeatJet c ψ 1 t x*scaledHeatJet c ψ 2 t x+
        scaledHeatJet c ψ 0 t x*scaledHeatJet c ψ 3 t x) t := by
  have hd := scaledHeatJet_time_expr hψ hc 2 ht x
  rw [JetExpr.burgers2] at hd
  simpa only [scaledHeatJet_expr hψ hc] using hd

lemma scaledHeatJet_time3 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0<c) {t : ℝ} (ht : 0<t) (x : ℝ) :
    HasDerivAt (fun s ↦ scaledHeatJet c ψ 3 s x)
      ((1/2 : ℝ)*scaledHeatJet c ψ 5 t x+3*(scaledHeatJet c ψ 2 t x)^2+
        4*scaledHeatJet c ψ 1 t x*scaledHeatJet c ψ 3 t x+
        scaledHeatJet c ψ 0 t x*scaledHeatJet c ψ 4 t x) t := by
  have hd := scaledHeatJet_time_expr hψ hc 3 ht x
  rw [JetExpr.burgers3] at hd
  simpa only [scaledHeatJet_expr hψ hc] using hd

end SKValue

end

end OAI
