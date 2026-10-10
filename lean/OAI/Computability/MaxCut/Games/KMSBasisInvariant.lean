import Mathlib
import OAI.Computability.MaxCut.Games.MatrixFourier
import OAI.Computability.MaxCut.Games.RowErasureSliceQuotient

namespace OAI

namespace MaxCutGames.Inverse.KMSBasisInvariant
noncomputable section
open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- The invertible change of the ordered domain basis. -/
def primalChange (g : E ≃ₗ[F2] E) : (E →ₗ[F2] F) ≃ (E →ₗ[F2] F) where
  toFun X := X.comp g.toLinearMap
  invFun X := X.comp g.symm.toLinearMap
  left_inv X := by ext x; simp
  right_inv X := by ext x; simp

/-- The contragredient reindexing used in the trace pairing. -/
def frequencyChange (g : E ≃ₗ[F2] E) : (F →ₗ[F2] E) ≃ (F →ₗ[F2] E) where
  toFun S := g.toLinearMap.comp S
  invFun S := g.symm.toLinearMap.comp S
  left_inv S := by ext x; simp
  right_inv S := by ext x; simp

def IsBasisInvariant (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (g : E ≃ₗ[F2] E) X, f (X.comp g.toLinearMap) = f X

theorem character_change (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E)
    (X : E →ₗ[F2] F) :
    linearTraceCharacter (g.toLinearMap.comp S) X =
      linearTraceCharacter S (X.comp g.toLinearMap) := by
  simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

variable [Fintype (E →ₗ[F2] F)]

/-- Invariance of the function transfers to its actual normalized coefficients. -/
theorem coefficient_change (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E) :
    linearCoeff f (g.toLinearMap.comp S) = linearCoeff f S := by
  unfold linearCoeff
  apply Fintype.expect_equiv (primalChange g)
  intro X
  change f X * (linearTraceCharacter (g.toLinearMap.comp S) X).re =
    f (X.comp g.toLinearMap) * (linearTraceCharacter S (X.comp g.toLinearMap)).re
  rw [character_change, hf g X]

/-- The degree is the rank of the actual dual linear map. -/
def frequencyRank (S : F →ₗ[F2] E) : ℕ := Module.finrank F2 (LinearMap.range S)

omit [Fintype (E →ₗ[F2] F)] in
theorem frequencyRank_change (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E) :
    frequencyRank (g.toLinearMap.comp S) = frequencyRank S := by
  unfold frequencyRank
  rw [LinearMap.range_comp, g.finrank_map_eq]

variable [Fintype (F →ₗ[F2] E)]

/-- Exact rank projection, defined directly by trace characters. -/
def rankProjection (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) : ℝ :=
  ∑ S, if frequencyRank S = i then linearCoeff f S * (linearTraceCharacter S X).re else 0

/-- Each rank projection preserves basis invariance. -/
theorem rankProjection_invariant (i : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) : IsBasisInvariant (rankProjection i f) := by
  intro g X
  unfold rankProjection
  apply Fintype.sum_equiv (frequencyChange g)
  intro S
  change (if frequencyRank S = i then
      linearCoeff f S * (linearTraceCharacter S (X.comp g.toLinearMap)).re else 0) =
    if frequencyRank (g.toLinearMap.comp S) = i then
      linearCoeff f (g.toLinearMap.comp S) *
        (linearTraceCharacter (g.toLinearMap.comp S) X).re else 0
  rw [frequencyRank_change, coefficient_change f hf, character_change]

end
end MaxCutGames.Inverse.KMSBasisInvariant

end OAI
