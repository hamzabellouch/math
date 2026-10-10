import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExpansionLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialUniform
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorUnweight
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorBoundedExpansion

namespace OAI

/-! Uniform convergence of the actual exterior value/derivative jets on a fixed tail. -/

open Polynomial Set Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialPolynomialFunction_uniform_limit (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (hP : ∀ k, k ≤ d → Tendsto (fun n => (P n).coeff k) atTop (nhds (Q.coeff k))) :
    TendstoUniformlyOn (fun n t => radialExteriorPolynomialFunction (P n) t)
      (radialExteriorPolynomialFunction Q) atTop (Ici (0 : ℝ)) := by
  have hu := radialPolynomial_eval_tendstoUniformly P Q d hdeg hQ hP
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) ε hε] with n hn t ht
  apply hn
  simp only [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have ht0 : 0 ≤ t := ht
  nlinarith

theorem radialPolynomialEuler_degree (P : ℂ[X]) (d : ℕ) (hd : P.natDegree ≤ d) :
    (radialPolynomialEuler P).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [radialPolynomialEuler_coeff,coeff_eq_zero_of_natDegree_lt (hd.trans_lt hk),mul_zero]

theorem radialExteriorUnweight_uniform_limit (κ : ℝ) (hκ : 0 ≤ κ)
    (v : ℕ → ℝ →ᵇ ℂ × ℂ) (w : ℝ →ᵇ ℂ × ℂ) (hv : Tendsto v atTop (nhds w)) :
    TendstoUniformlyOn (fun n => radialExteriorUnweight κ (v n))
      (radialExteriorUnweight κ w) atTop (Ici (0 : ℝ)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.mp hv).eventually (gt_mem_nhds hε)] with n hn t ht
  rw [dist_comm,dist_eq_norm]
  change ‖Real.exp (-κ*t) • v n t-Real.exp (-κ*t) • w t‖ < ε
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-κ*t) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have ht0 : 0 ≤ t := ht
    nlinarith)
  have hb := (v n-w).norm_coe_le_norm t
  change ‖v n t-w t‖ ≤ ‖v n-w‖ at hb
  calc
    _ ≤ 1*‖v n t-w t‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
    _ ≤ ‖v n-w‖ := by simpa only [one_mul] using hb
    _ < ε := hn

noncomputable def radialPolynomialJet (P : ℂ[X]) (t : ℝ) : ℂ × ℂ :=
  (radialExteriorPolynomialFunction P t,radialExteriorPolynomialFunction (radialPolynomialEuler P) t)

theorem radialPolynomialJet_uniform_limit (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (hP : ∀ k, k ≤ d → Tendsto (fun n => (P n).coeff k) atTop (nhds (Q.coeff k))) :
    TendstoUniformlyOn (fun n => radialPolynomialJet (P n)) (radialPolynomialJet Q)
      atTop (Ici (0 : ℝ)) := by
  have h0 := radialPolynomialFunction_uniform_limit P Q d hdeg hQ hP
  have h1 := radialPolynomialFunction_uniform_limit
    (fun n => radialPolynomialEuler (P n)) (radialPolynomialEuler Q) d
    (hdeg.mono (fun n hn => radialPolynomialEuler_degree (P n) d hn))
    (radialPolynomialEuler_degree Q d hQ)
    (fun k hk => by simpa only [radialPolynomialEuler_coeff] using (hP k hk).const_mul (-2*(k : ℂ)))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp h0) ε hε,
    (Metric.tendstoUniformlyOn_iff.mp h1) ε hε] with n hn0 hn1 t ht
  exact max_lt (hn0 t ht) (hn1 t ht)

theorem radialExterior_corrected_jet_uniform_limit (κ : ℝ) (hκ : 0 ≤ κ)
    (ν m : ℕ → ℂ) (ν₀ m₀ : ℂ)
    (hν : Tendsto ν atTop (nhds ν₀)) (hm : Tendsto m atTop (nhds m₀)) (hm₀ : ‖m₀‖ < 1)
    (j : ℕ) (v : ℕ → ℝ →ᵇ ℂ × ℂ) (w : ℝ →ᵇ ℂ × ℂ) (hv : Tendsto v atTop (nhds w)) :
    TendstoUniformlyOn
      (fun n t => radialPolynomialJet (radialExteriorExpansion (ν n) n (m n) j) t+
        radialExteriorUnweight κ (v n) t)
      (fun t => radialPolynomialJet (radialFreeExpansion ν₀ m₀ j) t+
        radialExteriorUnweight κ w t) atTop (Ici (0 : ℝ)) := by
  have hP := radialPolynomialJet_uniform_limit
    (fun n => radialExteriorExpansion (ν n) n (m n) j) (radialFreeExpansion ν₀ m₀ j) j
    (Eventually.of_forall (fun n => radialExteriorExpansion_degree _ _ _ _))
    (radialFreeExpansion_degree _ _ _)
    (fun k _ => radialExteriorExpansion_coefficient_limit ν m ν₀ m₀ hν hm hm₀ j k)
  exact hP.add (radialExteriorUnweight_uniform_limit κ hκ v w hv)

end DefocusingNLS

end OAI
