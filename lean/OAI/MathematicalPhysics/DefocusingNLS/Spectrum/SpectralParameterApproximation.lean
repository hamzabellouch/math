import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalParameterExpansion

namespace OAI

/-! Fixed polynomial families approximate the parameter derivative to arbitrary order. -/

open Filter Topology Polynomial
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonical_parameter_polynomial_approximation (ν η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0)
    (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn ν η b n L c Y) (z : ℂ) :
    ∃ P : ℕ → ℂ[X] × ℂ[X], ∀ J : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ t, 0 ≤ t →
      ‖(deriv (fun lam => Y lam t) z).1.1-radialExteriorPolynomialFunction (P J).1 t‖ ≤
        A*Real.exp (-(2*(J : ℝ))*t) ∧
      ‖(deriv (fun lam => Y lam t) z).2.1-radialExteriorPolynomialFunction (P J).2 t‖ ≤
        A*Real.exp (-(2*(J : ℝ))*t) := by
  classical
  choose j hj U v hv using fun J => canonical_circular_parameter_expansion
    ν η b n hn L hX hb c Y hY z J
  refine ⟨U,?_⟩
  intro J
  refine ⟨‖v J‖,norm_nonneg _,?_⟩
  intro t ht
  have hrate : Real.exp (-(2*(j J : ℝ))*t) ≤ Real.exp (-(2*(J : ℝ))*t) := by
    apply Real.exp_le_exp.mpr
    have hj' : (J : ℝ) ≤ j J := by exact_mod_cast hj J
    nlinarith
  have hbnd : ‖circularUnweight (2*(j J : ℝ)) (v J) t‖ ≤
      ‖v J‖*Real.exp (-(2*(J : ℝ))*t) := by
    exact (circularUnweight_norm (2*(j J : ℝ)) t (v J)).trans
      ((mul_le_mul_of_nonneg_right hrate (norm_nonneg _)).trans_eq (mul_comm _ _))
  have hp : (deriv (fun lam => Y lam t) z).1.1-
      radialExteriorPolynomialFunction (U J).1 t=
      (circularUnweight (2*(j J : ℝ)) (v J) t).1.1 := by
    rw [hv J t ht]
    simp only [circularPolynomialJet,Prod.fst_add,add_sub_cancel_left]
  have hm : (deriv (fun lam => Y lam t) z).2.1-
      radialExteriorPolynomialFunction (U J).2 t=
      (circularUnweight (2*(j J : ℝ)) (v J) t).2.1 := by
    rw [hv J t ht]
    simp only [circularPolynomialJet,Prod.snd_add,Prod.fst_add,add_sub_cancel_left]
  rw [hp,hm]
  exact ⟨(norm_fst_le _).trans ((norm_fst_le _).trans hbnd),
    (norm_fst_le _).trans ((norm_snd_le _).trans hbnd)⟩

end DefocusingNLS

end OAI
