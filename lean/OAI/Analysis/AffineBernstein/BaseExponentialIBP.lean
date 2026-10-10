import Mathlib
import OAI.Analysis.AffineBernstein.BaseWeightedIntegral

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma dirDeriv_exp_linear_combination {P F : E → ℝ} {x : E}
    (hP : DifferentiableAt ℝ P x) (hF : DifferentiableAt ℝ F x) (a b : ℝ) (v : E) :
    dirDeriv v (fun y => Real.exp (a*P y+b*F y)) x =
      Real.exp (a*P x+b*F x)*(a*dirDeriv v P x+b*dirDeriv v F x) := by
  have hh : HasFDerivAt (fun y => Real.exp (a*P y+b*F y))
      (Real.exp (a*P x+b*F x) • (a • fderiv ℝ P x+b • fderiv ℝ F x)) x :=
    ((hP.hasFDerivAt.const_mul a).add (hF.hasFDerivAt.const_mul b)).exp
  change fderiv ℝ _ x v = _
  rw [hh.fderiv]
  rfl

lemma flatCofactorPair_exp {P F : E → ℝ} {x : E}
    (hP : DifferentiableAt ℝ P x) (hF : DifferentiableAt ℝ F x)
    (f g : E → ℝ) (v : ι → E) (a b : ℝ) :
    flatCofactorPair f v (fun y => Real.exp (a*P y+b*F y)) g x =
      Real.exp (a*P x+b*F x)*(a*flatCofactorPair f v P g x+b*flatCofactorPair f v F g x) := by
  simp only [flatCofactorPair,dirDeriv_exp_linear_combination hP hF]
  simp only [mul_add,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma flatCofactorPair_test_square {σ : E → ℝ} {x : E}
    (hσ : DifferentiableAt ℝ σ x) (f g : E → ℝ) (v : ι → E) :
    flatCofactorPair f v (fun y => σ y*σ y) g x = 2*σ x*flatCofactorPair f v σ g x := by
  simp only [flatCofactorPair,dirDeriv_mul hσ hσ,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/- Base identity for the exact exponential weight and a squared compact test.
It is valid without global smooth extensions of the support function. -/
theorem integral_flatCofactor_exp_square {f P F g σ : E → ℝ} (v : ι → E)
    (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ)
    (hf : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ f x)
    (hP : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ P x)
    (hF : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ F x)
    (hg : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ g x) (a b : ℝ) :
    (∫ x, Real.exp (a*P x+b*F x)*σ x^2 *
      (flatCofactorTrace f v g x+a*flatCofactorPair f v P g x+b*flatCofactorPair f v F g x) ∂μ) =
      -2*(∫ x, Real.exp (a*P x+b*F x)*σ x*flatCofactorPair f v σ g x ∂μ) := by
  have hs : tsupport (fun x => σ x*σ x) ⊆ tsupport σ := tsupport_mul_subset_left
  have hh := integral_flatCofactor_trace (μ := μ) v (hσ.mul hσ) (hc.mul_left)
    (fun x hx => hf x (hs hx))
    (fun x hx => (((contDiffAt_const.mul (hP x (hs hx))).add
      (contDiffAt_const.mul (hF x (hs hx)))).exp))
    (fun x hx => hg x (hs hx)) (β := fun x => Real.exp (a*P x+b*F x))
  have hleft : (∫ x, (Real.exp (a*P x+b*F x)*flatCofactorTrace f v g x+
      flatCofactorPair f v (fun y => Real.exp (a*P y+b*F y)) g x)*(σ x*σ x) ∂μ) =
      (∫ x, Real.exp (a*P x+b*F x)*σ x^2 *
        (flatCofactorTrace f v g x+a*flatCofactorPair f v P g x+b*flatCofactorPair f v F g x) ∂μ) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp only
    by_cases hx : x ∈ tsupport σ
    · rw [flatCofactorPair_exp ((hP x hx).differentiableAt (by simp))
        ((hF x hx).differentiableAt (by simp))]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [hleft] at hh
  rw [hh]
  rw [← integral_const_mul]
  rw [← integral_neg]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [flatCofactorPair_test_square (hσ.differentiable (by simp) x)]
  ring

end AffineBernstein
end

end OAI
