import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondPoisson

namespace OAI

/-! # The retained second-transform frequencies have both signs -/

namespace Ostmann

open scoped SchwartzMap FourierTransform

theorem quadratic_schwartz_fourier_even (f : 𝓢(ℝ, ℂ)) (hf : Function.Even f) :
    Function.Even (𝓕 f : 𝓢(ℝ, ℂ)) := by
  intro x
  have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) (f : ℝ → ℂ) x
  have he : (f : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = f := by
    funext y
    exact hf y
  rw [he] at h
  exact h.symm

theorem quadraticFourierSquare_fourier_even (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    Function.Even (𝓕 (quadraticFourierSquare ρ a ha) : 𝓢(ℝ, ℂ)) :=
  quadratic_schwartz_fourier_even _ (quadraticFourierSquare_even ρ a ha)

theorem quadraticFourierSquare_signed_argument (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (l : ℤ) (Y : ℝ) :
    𝓕 (quadraticFourierSquare ρ a ha) ((l : ℝ) * Y) =
      𝓕 (quadraticFourierSquare ρ a ha) ((l.natAbs : ℝ) * Y) := by
  rcases le_total 0 l with hl | hl
  · have hi : (l.natAbs : ℤ) = l := by rw [Int.natCast_natAbs, abs_of_nonneg hl]
    have he : (l.natAbs : ℝ) = (l : ℝ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hi
    rw [he]
  · have he : (l : ℝ) = -((l.natAbs : ℕ) : ℝ) := by
      have hi : l = -(l.natAbs : ℤ) := by
        rw [Int.natCast_natAbs, abs_of_nonpos hl, neg_neg]
      simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun z : ℤ => (z : ℝ)) hi
    rw [he, neg_mul]
    exact quadraticFourierSquare_fourier_even ρ a ha _

end Ostmann

end OAI
