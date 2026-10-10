import OAI.Analysis.KadisonKastler.HilbertSumCorners
import OAI.Analysis.KadisonKastler.DirectIntegralConjugacy

namespace OAI

/-! # Coordinate corners of an operator with actual field action -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))

local notation "L" => fun n => Lp (K n) 2 (μ n)

theorem hilbertSumCompression_field_action
    (T : lp L 2 →L[ℂ] lp L 2) (F : ∀ n, X n → K n →L[ℂ] K n)
    (hT : ∀ (f : lp L 2) n, (T f) n =ᵐ[μ n] fun x => F n x (f n x)) (n : ℕ) :
    RepresentsOperatorField (μ n) (F n) (hilbertSumCompression n T) := by
  intro f
  simpa only [hilbertSumCompression_apply, lp.single_apply_self] using
    hT (lp.single 2 n f) n

theorem hilbertSum_field_diagonal
    (T : lp L 2 →L[ℂ] lp L 2) (F : ∀ n, X n → K n →L[ℂ] K n)
    (hT : ∀ (f : lp L 2) n, (T f) n =ᵐ[μ n] fun x => F n x (f n x))
    (f : lp L 2) (n : ℕ) : T f n = hilbertSumCompression n T (f n) := by
  apply Lp.ext
  exact (hT f n).trans (hilbertSumCompression_field_action μ T F hT n (f n)).symm

theorem hilbertSum_field_commutes_projection
    (T : lp L 2 →L[ℂ] lp L 2) (F : ∀ n, X n → K n →L[ℂ] K n)
    (hT : ∀ (f : lp L 2) n, (T f) n =ᵐ[μ n] fun x => F n x (f n x)) (n : ℕ) :
    hilbertSumProjection n * T = T * hilbertSumProjection n := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  change (hilbertSumProjection n (T f)) i = T (hilbertSumProjection n f) i
  rw [hilbertSum_field_diagonal μ T F hT (hilbertSumProjection n f) i]
  by_cases hi : i = n
  · subst i
    simp only [hilbertSumProjection_apply, lp.single_apply_self]
    exact hilbertSum_field_diagonal μ T F hT f n
  · simp only [hilbertSumProjection_apply, lp.single_apply_ne 2 n _ hi, map_zero]

end

end KadisonKastler

end OAI
