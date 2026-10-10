import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundedPolynomialAnalytic
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoefficientContinuity
import Mathlib.Topology.ContinuousMap.Bounded.Star

namespace OAI

/-! Bounded coefficient functions for the normalized actual-profile error. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem exists_bounded_normalized_coefficients (m : ℕ) (κ : ℝ)
    (q p e : ℝ →ᵇ ℂ)
    (hqe : ∀ t, 0 ≤ t → q t-p t=(Real.exp (-κ*t) : ℂ)*e t) :
    ∃ A B : ℝ →ᵇ ℂ, ∀ t, 0 ≤ t →
      A t=(Real.exp (κ*t) : ℂ)*(spectralDiagonalCoefficient m (q t)-
        spectralDiagonalCoefficient m (p t)) ∧
      B t=(Real.exp (κ*t) : ℂ)*(spectralCrossCoefficient m (q t)-
        spectralCrossCoefficient m (p t)) := by
  let M := max ‖q‖ ‖p‖
  obtain ⟨K,hK,hLip⟩ := spectralCoefficient_lipschitz m M
  let F : ℝ → ℂ × ℂ := fun t => Real.exp (κ*max t 0) •
    (spectralDiagonalCoefficient m (q (max t 0))-spectralDiagonalCoefficient m (p (max t 0)),
     spectralCrossCoefficient m (q (max t 0))-spectralCrossCoefficient m (p (max t 0)))
  have hF : Continuous F := by
    dsimp [F,spectralDiagonalCoefficient,spectralCrossCoefficient]
    fun_prop
  have hbound (t : ℝ) : ‖F t‖ ≤ K*‖e‖ := by
    let s := max t 0
    have hs : 0 ≤ s := le_max_right t 0
    have he : Real.exp (κ*s)*Real.exp (-κ*s)=1 := by
      rw [← Real.exp_add]
      simp
    have hdiff : ‖q s-p s‖ ≤ Real.exp (-κ*s)*‖e‖ := by
      rw [hqe s hs,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (e.norm_coe_le_norm s) (Real.exp_nonneg _)
    change ‖Real.exp (κ*s) • (_ : ℂ × ℂ)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (κ*s)*(K*‖q s-p s‖) :=
        mul_le_mul_of_nonneg_left (hLip (q s) (p s)
          ((q.norm_coe_le_norm s).trans (le_max_left _ _))
          ((p.norm_coe_le_norm s).trans (le_max_right _ _))) (Real.exp_nonneg _)
      _ ≤ Real.exp (κ*s)*(K*(Real.exp (-κ*s)*‖e‖)) := by gcongr
      _ = K*‖e‖ := by
        calc
          _ = (Real.exp (κ*s)*Real.exp (-κ*s))*(K*‖e‖) := by ring
          _ = _ := by rw [he,one_mul]
  let G : ℝ →ᵇ ℂ × ℂ := BoundedContinuousFunction.ofNormedAddCommGroup F hF (K*‖e‖) hbound
  refine ⟨(ContinuousLinearMap.fst ℂ ℂ ℂ).compLeftContinuousBounded ℝ G,
    (ContinuousLinearMap.snd ℂ ℂ ℂ).compLeftContinuousBounded ℝ G,?_⟩
  intro t ht
  change (F t).1=_ ∧ (F t).2=_
  simp [F,max_eq_left ht,Complex.real_smul]

noncomputable def boundedZeroFirst : (ℝ →ᵇ ℂ) →L[ℂ] (ℝ →ᵇ ℂ × ℂ) :=
  ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)).compLeftContinuousBounded ℝ

noncomputable def circularCoefficientForcing (A B f g : ℝ →ᵇ ℂ) : CircularTailSpace :=
  (boundedZeroFirst (A*f+B*g),boundedZeroFirst (star A*g+star B*f))

theorem circularCoefficientForcing_analyticAt (A B : ℝ →ᵇ ℂ)
    (f g : ℂ → ℝ →ᵇ ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    AnalyticAt ℂ (fun lam => circularCoefficientForcing A B (f lam) (g lam)) z := by
  have hp : AnalyticAt ℂ (fun lam => A*f lam+B*g lam) z :=
    (analyticAt_const.mul hf).add (analyticAt_const.mul hg)
  have hm : AnalyticAt ℂ (fun lam => star A*g lam+star B*f lam) z :=
    (analyticAt_const.mul hg).add (analyticAt_const.mul hf)
  exact (((boundedZeroFirst).analyticAt _).comp hp).prod
    (((boundedZeroFirst).analyticAt _).comp hm)

theorem circularCoefficientForcing_evaluation (A B f g : ℝ →ᵇ ℂ) (t : ℝ) :
    circularTailEvaluation (circularCoefficientForcing A B f g) t=
      circularCoefficientAction (A t) (B t) ((f t,0),(g t,0)) := rfl

theorem circularCoefficientForcing_normalized (A B f g : ℝ →ᵇ ℂ)
    (νp νm η : ℂ) (m : ℕ) (κ t : ℝ) (q p : ℂ)
    (Z : (ℂ × ℂ) × (ℂ × ℂ)) (hf : f t=Z.1.1) (hg : g t=Z.2.1)
    (hA : A t=(Real.exp (κ*t) : ℂ)*
      (spectralDiagonalCoefficient m q-spectralDiagonalCoefficient m p))
    (hB : B t=(Real.exp (κ*t) : ℂ)*
      (spectralCrossCoefficient m q-spectralCrossCoefficient m p)) :
    circularTailEvaluation (circularCoefficientForcing A B f g) t=
      Real.exp (κ*t) • (circularBoundedField νp νm η m q Z-
        circularBoundedField νp νm η m p Z) := by
  rw [circularCoefficientForcing_evaluation,circularBoundedField_coefficient_difference,hA,hB,hf,hg]
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [circularCoefficientAction,Prod.smul_mk,Complex.real_smul,star_mul,
      Complex.star_def,Complex.conj_ofReal]
  all_goals ring

end DefocusingNLS

end OAI
