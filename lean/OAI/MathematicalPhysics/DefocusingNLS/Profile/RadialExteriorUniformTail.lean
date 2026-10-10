import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorJetLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailData

namespace OAI

/-! Uniform convergence provides a single tail on which cutoff removal is valid. -/

open Polynomial Set Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radial_uniform_tail_near_limit {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → ℝ → E) (F₀ : ℝ → E) (m : E) (δ : ℝ) (hδ : 0 < δ)
    (hF : TendstoUniformlyOn F F₀ atTop (Ici (0 : ℝ)))
    (hF₀ : Tendsto F₀ atTop (nhds m)) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ᶠ n in atTop, ∀ t, S ≤ t → ‖F n t-m‖ < δ := by
  have he : ∀ᶠ t in atTop, ‖F₀ t-m‖ < δ/2 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hF₀).eventually (gt_mem_nhds (by positivity))
  obtain ⟨S,hS⟩ := eventually_atTop.mp he
  refine ⟨max S 0,le_max_right _ _,?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hF) (δ/2) (by positivity)] with n hn t ht
  have ht0 : 0 ≤ t := (le_max_right S 0).trans ht
  have h1 := hn t ht0
  rw [dist_comm,dist_eq_norm] at h1
  have h2 := hS t ((le_max_left S 0).trans ht)
  have hb : ‖F n t-m‖ ≤ ‖F n t-F₀ t‖+‖F₀ t-m‖ := by
    simpa only [dist_eq_norm] using dist_triangle (F n t) (F₀ t) m
  linarith

theorem radialPolynomialJet_tendsto (P : ℂ[X]) :
    Tendsto (radialPolynomialJet P) atTop (nhds (P.coeff 0,0)) := by
  have h0 := radialExteriorPolynomialFunction_tendsto P
  have h1 : Tendsto (radialExteriorPolynomialFunction (radialPolynomialEuler P)) atTop (nhds 0) := by
    simpa only [radialPolynomialEuler_coeff,Nat.cast_zero,mul_zero,zero_mul] using
      radialExteriorPolynomialFunction_tendsto (radialPolynomialEuler P)
  exact h0.prodMk_nhds h1

theorem radialExterior_corrected_jet_tendsto (κ : ℝ) (hκ : 0 < κ) (P : ℂ[X])
    (v : ℝ →ᵇ ℂ × ℂ) :
    Tendsto (fun t => radialPolynomialJet P t+radialExteriorUnweight κ v t) atTop
      (nhds (P.coeff 0,0)) := by
  simpa only [add_zero] using (radialPolynomialJet_tendsto P).add
    (radialExteriorUnweight_tendsto κ hκ v)

end DefocusingNLS

end OAI
