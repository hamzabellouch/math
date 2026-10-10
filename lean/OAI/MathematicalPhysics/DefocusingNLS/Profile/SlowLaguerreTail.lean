import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ShiftedSlowGrowth

namespace OAI

/-! # The two Laguerre tails of the actual slow solution

The finite-part definitions make the initial values explicit. Integration by
parts identifies them with coefficients of the first and second derivatives.
-/

open Filter Topology

namespace DefocusingNLS

noncomputable def slowLaguerreCoefficient (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  laguerreCoefficientIntegral (shiftedSlowDerivative 0 q m s) n

noncomputable def slowLaguerreB (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  shiftedSlowDerivative 0 q m s 0 - ∑ j ∈ Finset.range n, slowLaguerreCoefficient q m s j

noncomputable def slowLaguerreC (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  -shiftedSlowDerivative 1 q m s 0 - ∑ j ∈ Finset.range n, slowLaguerreB q m s (j + 1)

theorem shiftedSlowDerivative_coefficient_step (k n : ℕ) (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    laguerreCoefficientIntegral (shiftedSlowDerivative (k + 1) q m s) n =
      -shiftedSlowDerivative k q m s 0 +
        ∑ j ∈ Finset.range (n + 1),
          laguerreCoefficientIntegral (shiftedSlowDerivative k q m s) j := by
  apply laguerreCoefficientIntegral_derivative
  · intro t _
    exact hasDerivAt_shiftedSlowDerivative k q m s hq hsim t
  · exact (continuous_shiftedSlowDerivative k q m s hq hsim).continuousWithinAt
  · intro j
    exact integrableOn_laguerreIntegrand_shiftedSlowDerivative k j q m s hq hsre hsim
  · exact integrableOn_laguerreIntegrand_shiftedSlowDerivative (k + 1) n q m s hq hsre hsim

@[simp] theorem slowLaguerreB_zero (q : ℂ) (m : ℕ) (s : ℂ) :
    slowLaguerreB q m s 0 = regularizedSlowSolution q m (-s) := by
  simp [slowLaguerreB, shiftedSlowDerivative]

@[simp] theorem slowLaguerreC_zero (q : ℂ) (m : ℕ) (s : ℂ) :
    slowLaguerreC q m s 0 = -deriv (regularizedSlowSolution q m) (-s) := by
  simp [slowLaguerreC, shiftedSlowDerivative, iteratedDeriv_succ]

theorem slowLaguerreB_succ (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ) :
    slowLaguerreB q m s (n + 1) = slowLaguerreB q m s n - slowLaguerreCoefficient q m s n := by
  simp only [slowLaguerreB, Finset.sum_range_succ]
  ring

theorem slowLaguerreC_succ (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ) :
    slowLaguerreC q m s (n + 1) = slowLaguerreC q m s n - slowLaguerreB q m s (n + 1) := by
  simp only [slowLaguerreC, Finset.sum_range_succ]
  ring

theorem slowLaguerreB_eq_derivative_coefficient (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    slowLaguerreB q m s (n + 1) =
      -laguerreCoefficientIntegral (shiftedSlowDerivative 1 q m s) n := by
  have h := shiftedSlowDerivative_coefficient_step 0 n q m s hq hsre hsim
  change laguerreCoefficientIntegral (shiftedSlowDerivative 1 q m s) n =
    -shiftedSlowDerivative 0 q m s 0 +
      ∑ j ∈ Finset.range (n + 1), slowLaguerreCoefficient q m s j at h
  unfold slowLaguerreB
  linear_combination h

theorem slowLaguerreC_eq_derivative_coefficients (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    slowLaguerreC q m s n =
      laguerreCoefficientIntegral (shiftedSlowDerivative 2 q m s) n -
        laguerreCoefficientIntegral (shiftedSlowDerivative 1 q m s) n := by
  have h := shiftedSlowDerivative_coefficient_step 1 n q m s hq hsre hsim
  simp_rw [slowLaguerreC, slowLaguerreB_eq_derivative_coefficient q m s _ hq hsre hsim,
    Finset.sum_neg_distrib]
  rw [Finset.sum_range_succ] at h
  linear_combination -h

end DefocusingNLS

end OAI
