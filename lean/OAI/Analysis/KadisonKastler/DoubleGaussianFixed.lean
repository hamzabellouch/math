import OAI.Analysis.KadisonKastler.DoubleGaussianConstant
import OAI.Analysis.KadisonKastler.VectorStateSeparation

namespace OAI

/-! # Equality of the two real actions on doubly Gaussian-smoothed elements -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem doubleGaussian_diagonal_fixed
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hnU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hnV : ∀ t a, a ∈ M → unitaryConj (V t) a ∈ M)
    (hcomm : ∀ s t, Commute (U s : H →L[ℂ] H) (V t : H →L[ℂ] H))
    (hKU : VectorStateKMS M Ω U) (hKV : VectorStateKMS M Ω V)
    (a : H →L[ℂ] H) (ha : a ∈ M) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    doubleGaussianStateAverage U V hU hV a r hr t (-t) =
      doubleGaussianStateAverage U V hU hV a r hr 0 0 := by
  apply eq_of_vectorState_right_products Ω hsep
  · exact gaussianStateAverage_mem U hU M hnU _
      (gaussianStateAverage_mem V hV M hnV a ha r hr (-t)) r hr t
  · exact gaussianStateAverage_mem U hU M hnU _
      (gaussianStateAverage_mem V hV M hnV a ha r hr 0) r hr 0
  · intro b hb
    exact doubleGaussian_diagonal_coefficient_constant Ω U V hU hV hnU hnV hcomm hKU hKV
      a b ha hb r hr t

end

end KadisonKastler

end OAI
