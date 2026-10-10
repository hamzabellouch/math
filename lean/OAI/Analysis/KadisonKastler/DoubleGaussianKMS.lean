import OAI.Analysis.KadisonKastler.GaussianKMSShift
import OAI.Analysis.KadisonKastler.GaussianStateCoefficient

namespace OAI

/-! # KMS shifts in both coordinates of a doubly averaged element -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def doubleGaussianStateAverage (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z w : ℂ) : H →L[ℂ] H :=
  gaussianStateAverage U hU (gaussianStateAverage V hV a r hr w) r hr z

theorem doubleGaussianStateAverage_first_shift
    (hnU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hnV : ∀ t a, a ∈ M → unitaryConj (V t) a ∈ M)
    (hKU : VectorStateKMS M Ω U) (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M)
    (r : ℝ) (hr : 0 < r) (z w : ℂ) :
    productVectorState Ω (doubleGaussianStateAverage U V hU hV a r hr (z + Complex.I) w * b) =
      productVectorState Ω (b * doubleGaussianStateAverage U V hU hV a r hr z w) :=
  gaussianStateAverage_kms_shift Ω U hU hnU hKU _
    (gaussianStateAverage_mem V hV M hnV a ha r hr w) b hb r hr z

theorem doubleGaussianStateAverage_second_shift
    (hnU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hcomm : ∀ s t, Commute (U s : H →L[ℂ] H) (V t : H →L[ℂ] H))
    (hnV : ∀ t a, a ∈ M → unitaryConj (V t) a ∈ M)
    (hKV : VectorStateKMS M Ω V) (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M)
    (r : ℝ) (hr : 0 < r) (z w : ℂ) :
    productVectorState Ω (doubleGaussianStateAverage U V hU hV a r hr z (w + Complex.I) * b) =
      productVectorState Ω (b * doubleGaussianStateAverage U V hU hV a r hr z w) := by
  unfold doubleGaussianStateAverage
  rw [gaussianStateAverage_mul_right, gaussianStateAverage_mul_left]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold stateActionOrbit
  rw [gaussianStateAverage_conjugate V hV a _ (hcomm _) r hr (w + Complex.I),
    gaussianStateAverage_conjugate V hV a _ (hcomm _) r hr w]
  rw [gaussianStateAverage_kms_shift Ω V hV hnV hKV _ (hnU _ a ha) b hb r hr w]

end

end KadisonKastler

end OAI
