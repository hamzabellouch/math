import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExponentialInterpolation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

/-! Coarse ODE derivative growth upgrades arbitrary-order outgoing expansions. -/

open Set Polynomial
open scoped ContDiff
namespace DefocusingNLS

theorem radial_contDiffOn_iteratedDeriv (F : ℝ → ℂ) (L : ℝ)
    (hF : ContDiffOn ℝ ∞ F (Ioi L)) (k : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv k F) (Ioi L) := by
  induction k with
  | zero => simpa using hF
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

theorem radialPolynomialFunction_contDiff (P : ℂ[X]) :
    ContDiff ℝ ∞ (radialExteriorPolynomialFunction P) := by
  have heR : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-2*t)) := by fun_prop
  have he : ContDiff ℝ ∞ (fun t : ℝ => (Real.exp (-2*t) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp heR
  change ContDiff ℝ ∞ (fun t : ℝ => P.eval (Real.exp (-2*t) : ℂ))
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [radialExteriorPolynomialFunction, eval_add] using hP.add hQ
  | monomial n a =>
    simpa only [radialExteriorPolynomialFunction, eval_monomial] using
      (contDiff_const (c := a)).mul (he.pow n)

theorem radial_expansion_derivative_selection (F : ℝ → ℂ) (P : ℕ → ℂ[X]) (L : ℝ)
    (hF : ContDiffOn ℝ ∞ F (Ioi L))
    (hgrowth : ∀ k : ℕ, ∃ C B T : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ t, T ≤ t → ‖iteratedDeriv k F t‖ ≤ B*Real.exp (C*t))
    (happrox : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ A T : ℝ, 0 ≤ A ∧
      ∀ t, T ≤ t → ‖F t-radialExteriorPolynomialFunction (P j) t‖ ≤
        A*Real.exp (-(2*(j : ℝ))*t)) :
    ∀ k : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ A T : ℝ, 0 ≤ A ∧
      ∀ t, T ≤ t → ‖iteratedDeriv k (F-radialExteriorPolynomialFunction (P j)) t‖ ≤
        A*Real.exp (-R*t) := by
  intro k
  induction k with
  | zero =>
    intro R hR J
    obtain ⟨K,hK⟩ := exists_nat_gt R
    obtain ⟨j,hj,A,T,hA,hB⟩ := happrox (max J K)
    refine ⟨j,(le_max_left J K).trans hj,A,max T 0,hA,?_⟩
    intro t ht
    have ht0 : 0 ≤ t := (le_max_right T 0).trans ht
    have hjR : R ≤ 2*(j : ℝ) := by
      have hKj : (K : ℝ) ≤ j := by exact_mod_cast (le_max_right J K).trans hj
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
    apply (hB t ((le_max_left T 0).trans ht)).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    nlinarith
  | succ k ih =>
    intro R hR J
    obtain ⟨C,B,Tg,hC,hB,hgrow⟩ := hgrowth (k+2)
    obtain ⟨j,hj,A,Ta,hA,hap⟩ := ih (2*R+C) (by positivity) J
    obtain ⟨D,hD,hpoly⟩ := radialExteriorPolynomial_deriv_bounded (P j) (k+2)
    let H := F-radialExteriorPolynomialFunction (P j)
    have hH : ContDiffOn ℝ ∞ H (Ioi L) :=
      hF.sub (radialPolynomialFunction_contDiff (P j)).contDiffOn
    have hkH := radial_contDiffOn_iteratedDeriv H L hH k
    let T := max (L+1) (max Ta (max Tg 0))
    have hTL : L < T := lt_of_lt_of_le (by linarith : L < L+1) (le_max_left _ _)
    have hTa : Ta ≤ T := (le_max_left Ta _).trans (le_max_right _ _)
    have hTg : Tg ≤ T := (le_max_left Tg 0).trans
      ((le_max_right Ta _).trans (le_max_right _ _))
    have hT0 : 0 ≤ T := (le_max_right Tg 0).trans
      ((le_max_right Ta _).trans (le_max_right _ _))
    have hsmall : ∀ t, T ≤ t → ‖iteratedDeriv k H t‖ ≤ A*Real.exp (-(2*R+C)*t) :=
      fun t ht => hap t (hTa.trans ht)
    have hsecond : ∀ t, T ≤ t →
        ‖deriv (deriv (iteratedDeriv k H)) t‖ ≤ (B+D)*Real.exp (C*t) := by
      intro t ht
      have hLt : L < t := hTL.trans_le ht
      have ht0 : 0 ≤ t := hT0.trans ht
      have hf : ContDiffAt ℝ (k+2) F t :=
        (hF t hLt).contDiffAt (Ioi_mem_nhds hLt) |>.of_le (by simp)
      have hp : ContDiffAt ℝ (k+2) (radialExteriorPolynomialFunction (P j)) t :=
        (radialPolynomialFunction_contDiff (P j)).contDiffAt.of_le (by simp)
      have hd : deriv (deriv (iteratedDeriv k H))=iteratedDeriv (k+2) H := by
        rw [show k+2=(k+1)+1 by omega,iteratedDeriv_succ,iteratedDeriv_succ]
      rw [hd,show H=F-radialExteriorPolynomialFunction (P j) from rfl,
        iteratedDeriv_sub hf hp]
      calc
        _ ≤ ‖iteratedDeriv (k+2) F t‖+
            ‖iteratedDeriv (k+2) (radialExteriorPolynomialFunction (P j)) t‖ := norm_sub_le _ _
        _ ≤ B*Real.exp (C*t)+D := add_le_add (hgrow t (hTg.trans ht)) (hpoly t ht0)
        _ ≤ B*Real.exp (C*t)+D*Real.exp (C*t) := by
          exact add_le_add le_rfl (le_mul_of_one_le_right hD
            (Real.one_le_exp_iff.mpr (mul_nonneg hC ht0)))
        _ = _ := by ring
    refine ⟨j,hj,2*A+(B+D)*Real.exp C,T,by positivity,?_⟩
    intro t ht
    have hdf : ∀ s, T ≤ s → DifferentiableAt ℝ (iteratedDeriv k H) s := by
      intro s hs
      have hLs : L < s := hTL.trans_le hs
      exact ((hkH s hLs).contDiffAt (Ioi_mem_nhds hLs)).differentiableAt (by simp)
    have hddf : ∀ s, T ≤ s → DifferentiableAt ℝ (deriv (iteratedDeriv k H)) s := by
      intro s hs
      have hLs : L < s := hTL.trans_le hs
      exact (((hkH.deriv_of_isOpen (m := ∞) isOpen_Ioi (by simp)) s hLs).contDiffAt
        (Ioi_mem_nhds hLs)).differentiableAt (by simp)
    simpa only [iteratedDeriv_succ] using radial_derivative_exp_interpolation
      (iteratedDeriv k H) T A (B+D) C R t hA (add_nonneg hB hD) hC hR ht
      (hT0.trans ht) hdf hddf hsmall hsecond

end DefocusingNLS

end OAI
