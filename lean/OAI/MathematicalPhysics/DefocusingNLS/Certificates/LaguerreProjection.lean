import OAI.MathematicalPhysics.DefocusingNLS.Certificates.LaguerreIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! # Differentiation in Laguerre coefficients

Integration by parts gives the triangular derivative rule directly. No
interchange of an infinite Laguerre expansion and differentiation is needed.
-/

open Filter Topology MeasureTheory Set

namespace DefocusingNLS

noncomputable def laguerreValue (n : ℕ) (t : ℝ) : ℂ :=
  (laguerrePolynomial n).eval (t : ℂ)

noncomputable def laguerreIntegrand (f : ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (Real.exp (-t) : ℂ) * f t * laguerreValue n t

noncomputable def laguerreCoefficientIntegral (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), laguerreIntegrand f n t

theorem hasDerivAt_laguerreValue (n : ℕ) (t : ℝ) :
    HasDerivAt (laguerreValue n) (-∑ j ∈ Finset.range n, laguerreValue j t) t := by
  have h := ((laguerrePolynomial n).hasDerivAt (t : ℂ)).comp_ofReal
  rw [laguerrePolynomial_derivative] at h
  convert! h using 1
  simp only [Polynomial.eval_neg, Polynomial.eval_finsetSum, laguerreValue]

theorem hasDerivAt_laguerreIntegrand (f f' : ℝ → ℂ) (n : ℕ) (t : ℝ)
    (hf : HasDerivAt f (f' t) t) :
    HasDerivAt (laguerreIntegrand f n)
      (laguerreIntegrand f' n t - laguerreIntegrand f n t -
        ∑ j ∈ Finset.range n, laguerreIntegrand f j t) t := by
  have he := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).ofReal_comp
  have h := (he.fun_mul hf).fun_mul (hasDerivAt_laguerreValue n t)
  convert! h using 1
  simp only [laguerreIntegrand, neg_mul, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_one, mul_neg, Finset.mul_sum, Function.comp_apply]
  ring

/-- A weighted derivative coefficient is a finite partial sum minus the
boundary value. Both endpoint limits follow from the integrability hypotheses. -/
theorem laguerreCoefficientIntegral_derivative (f f' : ℝ → ℂ) (n : ℕ)
    (hf : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hc : ContinuousWithinAt f (Ici 0) 0)
    (hi : ∀ j, IntegrableOn (laguerreIntegrand f j) (Ioi 0))
    (hi' : IntegrableOn (laguerreIntegrand f' n) (Ioi 0)) :
    laguerreCoefficientIntegral f' n =
      -f 0 + ∑ j ∈ Finset.range (n + 1), laguerreCoefficientIntegral f j := by
  let D : ℝ → ℂ := fun t => laguerreIntegrand f' n t - laguerreIntegrand f n t -
    ∑ j ∈ Finset.range n, laguerreIntegrand f j t
  have hsum : IntegrableOn (fun t => ∑ j ∈ Finset.range n, laguerreIntegrand f j t)
      (Ioi 0) := integrable_finsetSum _ (fun j _ => hi j)
  have hD : IntegrableOn D (Ioi 0) := (hi'.sub (hi n)).sub hsum
  have hd (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      HasDerivAt (laguerreIntegrand f n) (D t) t :=
    hasDerivAt_laguerreIntegrand f f' n t (hf t ht)
  have hcont : ContinuousWithinAt (laguerreIntegrand f n) (Ici 0) 0 := by
    have hp : ContinuousWithinAt (laguerreValue n) (Ici 0) 0 :=
      (hasDerivAt_laguerreValue n 0).continuousAt.continuousWithinAt
    have he : ContinuousAt (fun t : ℝ => (Real.exp (-t) : ℂ)) 0 := by fun_prop
    exact (he.continuousWithinAt.mul hc).mul hp
  have hlim := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hd hD (hi n)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hD hlim
  have hz : laguerreIntegrand f n 0 = f 0 := by
    simp [laguerreIntegrand, laguerreValue]
  rw [hz, zero_sub] at h
  dsimp only [D] at h
  have hisub : IntegrableOn (fun t => laguerreIntegrand f' n t -
      laguerreIntegrand f n t) (Ioi 0) := hi'.sub (hi n)
  rw [integral_sub hisub hsum, integral_sub hi' (hi n),
    integral_finsetSum _ (fun j _ => hi j)] at h
  change laguerreCoefficientIntegral f' n - laguerreCoefficientIntegral f n -
    ∑ j ∈ Finset.range n, laguerreCoefficientIntegral f j = -f 0 at h
  rw [Finset.sum_range_succ]
  linear_combination h

end DefocusingNLS

end OAI
