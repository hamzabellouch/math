import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import OAI.NumberTheory.Ostmann.Construction.WordHistoryCoefficient

namespace OAI

/-! # Conjugated leaves use the same Fourier profile at the signed frequency -/

namespace Ostmann

open scoped FourierTransform SchwartzMap ComplexConjugate
open MeasureTheory

theorem real_schwartz_fourier_conj (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (t : ℝ) :
    conj (𝓕 ψ t) = 𝓕 ψ (-t) := by
  change conj (𝓕 (ψ : ℝ → ℂ) t) = 𝓕 (ψ : ℝ → ℂ) (-t)
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul, map_mul, hreal, ← Complex.exp_conj]
  congr 2
  norm_num [inner]
  exact Or.inl (map_natCast (starRingEnd ℂ) 2)

theorem normalizedFourierProfile_conj (ψ : ℝ → ℂ)
    (hψ : ∀ x, conj (ψ x) = ψ (-x)) (v z : ℝ) :
    conj (normalizedFourierProfile ψ v z) = normalizedFourierProfile ψ (-v) z := by
  simp only [normalizedFourierProfile, map_mul, Complex.conj_ofReal, hψ]
  congr 1
  congr 1
  ring

/-- The real physical smoothing function supplies the required symmetry;
there is no additional analytic hypothesis on the Fourier profile. -/
theorem normalizedFourierProfile_fourier_conj (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (v z : ℝ) :
    conj (normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v z) =
      normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) (-v) z :=
  normalizedFourierProfile_conj (𝓕 ψ : 𝓢(ℝ, ℂ)) (real_schwartz_fourier_conj ψ hreal) v z

/-- Arbitrarily conjugated bottom leaves are all represented by the existing
unsigned formula family with their actual signed frequency parameters. -/
theorem signedFourierLeaves {n : ℕ} (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (v z : Fin n → ℝ) (sign : Fin n → Bool) :
    (∏ j, if sign j then normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) (v j) (z j)
      else conj (normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) (v j) (z j))) =
      ∏ j, normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) (if sign j then v j else -v j) (z j) := by
  apply Finset.prod_congr rfl
  intro j _
  cases hs : sign j
  · exact normalizedFourierProfile_fourier_conj ψ hreal (v j) (z j)
  · rfl

end Ostmann

end OAI
