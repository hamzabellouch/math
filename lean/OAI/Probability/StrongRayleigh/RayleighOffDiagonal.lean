import OAI.Probability.StrongRayleigh.BivariateStability
import OAI.Probability.StrongRayleigh.PairCoefficients
import OAI.Probability.StrongRayleigh.TwoCoordinateCoefficients
import OAI.Probability.StrongRayleigh.TiltScaling

namespace OAI

universe u_1

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336AdditiveD139

theorem StronglyRayleighFinite.tiltCovariance_nonpos
    {F : Type u_1} [Fintype F] {μ : ProbabilityMeasure (F → Bool)}
    (hμ : StronglyRayleighFinite μ) (h : F → ℝ)
    (i j : F) (hij : i ≠ j) : tiltCovariance μ h i j ≤ 0 := by
  classical
  let weight : (F → Bool) → ℝ := fun x =>
    Real.exp (∑ k : F, h k * boolReal (x k)) *
      ((μ : Measure (F → Bool)) {x}).toReal
  let coeff (p q : Bool) (t : ℝ) : ℂ :=
    twoCoordinateCoefficient (fun x => (weight x : ℂ)) i j
      (fun _ => 1 + (t : ℂ) * Complex.I) p q
  have hcont (p q : Bool) : ContinuousAt (coeff p q) 0 := by
    apply Continuous.continuousAt
    exact (continuous_twoCoordinateCoefficient
      (fun x => (weight x : ℂ)) i j p q).comp (by fun_prop)
  have hzero (p q : Bool) : coeff p q 0 = (tiltPairMass μ h i j p q : ℂ) := by
    simpa [coeff, twoCoordinateWeight, tiltPairMass, weight] using
      (twoCoordinateWeight_cast_eq_coefficient weight i j p q).symm
  apply tiltCovariance_nonpos_of_pairMass
  apply bivariate_continuous_limit_rayleigh
    (coeff false false) (coeff true false) (coeff false true) (coeff true true)
    _ _ _ _ (hcont _ _) (hcont _ _) (hcont _ _) (hcont _ _)
    (hzero _ _) (hzero _ _) (hzero _ _) (hzero _ _)
  intro t ht z w hz hw
  let field := twoCoordinateField i j (fun _ : F => 1 + (t : ℂ) * Complex.I) z w
  have hfield (k : F) : 0 < (field k).im := by
    simp only [field, twoCoordinateField]
    split_ifs
    · exact hz
    · exact hw
    · simpa using ht
  have hstable := hμ (fun k => (Real.exp (h k) : ℂ) * field k) (fun k => by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_pos (Real.exp_pos (h k)) (hfield k))
  have hscale : finiteGeneratingValue μ (fun k => (Real.exp (h k) : ℂ) * field k) =
      ∑ x : F → Bool, (weight x : ℂ) *
        ∏ k : F, if x k = true then field k else 1 := by
    unfold finiteGeneratingValue
    apply Finset.sum_congr rfl
    intro x hx
    rw [generating_monomial_rescale]
    simp only [weight, Complex.ofReal_mul]
    ring
  rw [hscale, weighted_generating_two_coordinates _ _ i j hij z w] at hstable
  exact hstable

end Problem336AdditiveD139

end

end OAI
