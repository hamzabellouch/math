import OAI.NumberTheory.JointDickman.Probability.HistogramFourierRegularity
import OAI.NumberTheory.JointDickman.Amplification.GeometricSampledIntegral

namespace OAI

/-! # Exact finite-sum identities for the integrated histogram replacement -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

theorem integral_oppositeProductSum {q : ℕ} [NeZero q]
    (P : ZMod q → Prop) [DecidablePred P] (W : ℝ → ℂ)
    (A B : ℝ → ZMod q → ℂ)
    (hI : ∀ r, Integrable (fun ξ => W ξ*(A ξ r*B ξ (-r)))) :
    (∫ ξ : ℝ, W ξ*oppositeProductSum P (A ξ) (B ξ)) =
      ∑ r : ZMod q, if P r then ∫ ξ : ℝ, W ξ*(A ξ r*B ξ (-r)) else 0 := by
  have he : (fun ξ => W ξ*oppositeProductSum P (A ξ) (B ξ)) =
      fun ξ => ∑ r : ZMod q, if P r then W ξ*(A ξ r*B ξ (-r)) else 0 := by
    funext ξ
    simp only [oppositeProductSum,mul_sum,mul_ite,mul_zero]
  rw [he,integral_finsetSum]
  · apply sum_congr rfl
    intro r _
    by_cases hr : P r <;> simp only [hr,ite_true,ite_false,integral_zero]
  · intro r _
    by_cases hr : P r
    · simpa only [hr,ite_true] using hI r
    · simp only [hr,ite_false]
      exact integrable_zero ℝ ℂ volume

theorem manuscriptSampledIntegralError_eq {m B q : ℕ} [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (F G : ℝ → ℝ → ℂ)
    (P : ZMod q → Prop) [DecidablePred P] (w : 𝓢(ℝ,ℝ))
    (hI : ∀ r, Integrable (fun ξ => testFourierTransform w ξ*
      (manuscriptFourier m B q J g (F ξ) r*manuscriptFourier m B q J h (G ξ) (-r))))
    (hJ : ∀ r, Integrable (fun ξ => testFourierTransform w ξ*
      (sampledProjectedFourier m B q J g (fun i => F ξ (channelLower (channelFineCount m B) i)) r*
        sampledProjectedFourier m B q J h (fun i => G ξ (channelLower (channelFineCount m B) i)) (-r)))) :
    manuscriptSampledIntegralError m B q J g h F G P w =
      (∑ r : ZMod q, if P r then ∫ ξ : ℝ, testFourierTransform w ξ*
        (manuscriptFourier m B q J g (F ξ) r*manuscriptFourier m B q J h (G ξ) (-r)) else 0)-
      (∑ r : ZMod q, if P r then ∫ ξ : ℝ, testFourierTransform w ξ*
        (sampledProjectedFourier m B q J g (fun i => F ξ (channelLower (channelFineCount m B) i)) r*
          sampledProjectedFourier m B q J h (fun i => G ξ (channelLower (channelFineCount m B) i)) (-r)) else 0) := by
  have hsum (A C : ℝ → ZMod q → ℂ)
      (hh : ∀ r, Integrable (fun ξ => testFourierTransform w ξ*(A ξ r*C ξ (-r)))) :
      Integrable (fun ξ => testFourierTransform w ξ*oppositeProductSum P (A ξ) (C ξ)) := by
    have he : (fun ξ => testFourierTransform w ξ*oppositeProductSum P (A ξ) (C ξ)) =
        fun ξ => ∑ r : ZMod q, if P r then testFourierTransform w ξ*(A ξ r*C ξ (-r)) else 0 := by
      funext ξ
      simp only [oppositeProductSum,mul_sum,mul_ite,mul_zero]
    rw [he]
    apply integrable_finsetSum
    intro r _
    by_cases hr : P r
    · simpa only [hr,ite_true] using hh r
    · simp only [hr,ite_false]
      exact integrable_zero ℝ ℂ volume
  unfold manuscriptSampledIntegralError
  simp_rw [mul_sub]
  rw [integral_sub (hsum _ _ hI) (hsum _ _ hJ),
    integral_oppositeProductSum P _ _ _ hI,integral_oppositeProductSum P _ _ _ hJ]

end JointDickman

end OAI
