import OAI.Analysis.KadisonKastler.DoubleGaussianKMS

namespace OAI

/-! # Covariance of double Gaussian smearing -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryRealGroup_commute
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (s t : Multiplicative ℝ) :
    Commute (U s : H →L[ℂ] H) (U t : H →L[ℂ] H) := by
  have he : U s * U t = U t * U s := by rw [← map_mul, ← map_mul, mul_comm]
  exact congrArg Subtype.val he

variable (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem doubleGaussian_conjugate
    (u : unitary (H →L[ℂ] H))
    (hcU : ∀ t, Commute (u : H →L[ℂ] H) (U t : H →L[ℂ] H))
    (hcV : ∀ t, Commute (u : H →L[ℂ] H) (V t : H →L[ℂ] H))
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z w : ℂ) :
    unitaryConj u (doubleGaussianStateAverage U V hU hV a r hr z w) =
      doubleGaussianStateAverage U V hU hV (unitaryConj u a) r hr z w := by
  unfold doubleGaussianStateAverage
  rw [gaussianStateAverage_conjugate U hU _ u hcU,
    gaussianStateAverage_conjugate V hV a u hcV]

theorem doubleGaussian_first_covariance (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r)
    (z w : ℂ) (s : ℝ) :
    unitaryConj (U (Multiplicative.ofAdd s))
      (doubleGaussianStateAverage U V hU hV a r hr z w) =
    doubleGaussianStateAverage U V hU hV a r hr (z + s) w :=
  gaussianStateAverage_covariance U hU _ r hr z s

theorem doubleGaussian_second_covariance
    (hcomm : ∀ s t, Commute (U s : H →L[ℂ] H) (V t : H →L[ℂ] H))
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z w : ℂ) (s : ℝ) :
    unitaryConj (V (Multiplicative.ofAdd s))
      (doubleGaussianStateAverage U V hU hV a r hr z w) =
    doubleGaussianStateAverage U V hU hV a r hr z (w + s) := by
  unfold doubleGaussianStateAverage
  rw [gaussianStateAverage_conjugate U hU _ _ (fun t => (hcomm t _).symm),
    gaussianStateAverage_covariance V hV a r hr w s]

end

end KadisonKastler

end OAI
