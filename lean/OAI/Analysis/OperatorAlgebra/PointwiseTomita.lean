import OAI.Analysis.OperatorAlgebra.PointwiseAntiunitary
import OAI.Analysis.ModularTheory.CommutantExpectation

namespace OAI

/-! Commutation under the amplified Tomita conjugation. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma antiunitaryConjugate_mul (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (A B : H →L[ℂ] H) :
    antiunitaryConjugate J (A * B) = antiunitaryConjugate J A * antiunitaryConjugate J B := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [antiunitaryConjugate_apply, mul_apply_eq_comp]
  rw [hJ (B (J x))]

lemma antiunitaryConjugate_commute (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {A B : H →L[ℂ] H} (h : Commute A B) :
    Commute (antiunitaryConjugate J A) (antiunitaryConjugate J B) := by
  change _ * _ = _ * _
  rw [← antiunitaryConjugate_mul J hJ, ← antiunitaryConjugate_mul J hJ, h.eq]

lemma antiunitaryConjugate_commute_iff (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (A B : H →L[ℂ] H) :
    Commute A (antiunitaryConjugate J B) ↔ Commute (antiunitaryConjugate J A) B := by
  constructor <;> intro h
  · simpa only [antiunitaryConjugate_involutive J hJ] using antiunitaryConjugate_commute J hJ h
  · simpa only [antiunitaryConjugate_involutive J hJ] using antiunitaryConjugate_commute J hJ h

variable [CompleteSpace H]

lemma pointwiseTomita_commute_iff (μ : Measure ℝ) (S : BoundedRecovery.StandardModularData H)
    (A : H →L[ℂ] H) (R : Lp H 2 μ →L[ℂ] Lp H 2 μ) :
    Commute (pointwiseLpRepresentation μ A)
      (antiunitaryConjugate (pointwiseAntiunitary μ S.J) R) ↔
    Commute (pointwiseLpRepresentation μ (S.jConjugate A)) R := by
  rw [antiunitaryConjugate_commute_iff _
    (pointwiseAntiunitary_involutive μ S.J S.conjugation), pointwiseAntiunitary_conjugate]
  rfl

end WeakPureInfiniteness

end

end OAI
