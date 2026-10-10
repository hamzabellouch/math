import OAI.NumberTheory.Ostmann.Quadratic.QuadraticEvenFourier
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondScale

namespace OAI

/-! # The literal retained Fourier frequency is a positive square-root weight -/

namespace Ostmann

open scoped SchwartzMap FourierTransform

theorem quadratic_second_scale_factor {M : ℝ} {e b : ℕ}
    (hM : 0 < M) (he : 0 < e) (hb : 0 < b) (s t : ℕ) :
    quadraticSecondScale M e (s * t) b =
      Real.sqrt ((e : ℝ) / (M * b)) * Real.sqrt ((s : ℝ) * t) := by
  unfold quadraticSecondScale
  rw [Nat.cast_mul, show (e : ℝ) * ((s : ℝ) * t) / (M * b) =
    ((e : ℝ) / (M * b)) * ((s : ℝ) * t) by ring,
    Real.sqrt_mul (by positivity)]

theorem quadratic_middle_frequency_argument (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {M : ℝ} {e b : ℕ} (hM : 0 < M) (he : 0 < e) (hb : 0 < b)
    (l : ℤ) (d s t : ℕ) :
    𝓕 (quadraticFourierSquare ρ a ha)
      ((l : ℝ) * (quadraticSecondScale M e (s * t) b / d)) =
    𝓕 (quadraticFourierSquare ρ a ha)
      (((l.natAbs : ℝ) / d * Real.sqrt ((e : ℝ) / (M * b))) *
        Real.sqrt ((s : ℝ) * t)) := by
  rw [quadraticFourierSquare_signed_argument,
    quadratic_second_scale_factor hM he hb]
  congr 1
  ring

theorem quadratic_middle_parameter_pos {M : ℝ} {e b d : ℕ} {l : ℤ}
    (hM : 0 < M) (he : 0 < e) (hb : 0 < b) (hd : 0 < d) (hl : l ≠ 0) :
    0 < (l.natAbs : ℝ) / d * Real.sqrt ((e : ℝ) / (M * b)) := by
  have hl₀ : 0 < l.natAbs := Int.natAbs_pos.mpr hl
  positivity

end Ostmann

end OAI
