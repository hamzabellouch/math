import OAI.MeasureTheory.Falconer.Recursion.UniformProfileContact
import OAI.MeasureTheory.Falconer.Recursion.RoundedProfileContact

namespace OAI

/-! # Uniform integer-depth margins from the compactness contact theorem -/

namespace Falconer

theorem uniform_contact_depth_bounds {A B γ : ℝ} (hγ : 0 < γ)
    (hA : γ ≤ A) (hAB : A+γ ≤ B) (hB : B+γ ≤ 1) (hBA : B+γ ≤ 2*A)
    {N : ℕ} (hN : 0 < N) (hlarge : 4 ≤ γ*(N:ℝ)) :
    let a := Nat.floor (A*(N:ℝ))
    let b := Nat.floor (B*(N:ℝ))
    a ≤ b ∧ b ≤ N ∧ (γ/2)*(N:ℝ) ≤ (a:ℝ) ∧
      (γ/2)*(N:ℝ) ≤ (b-a:ℕ) ∧ γ*(N:ℝ) ≤ (N-b:ℕ) ∧
      (γ/2)*(N:ℝ) ≤ 2*(a:ℝ)-(b:ℝ) := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hA0 : 0 ≤ A := hγ.le.trans hA
  have hB0 : 0 ≤ B := by linarith
  have hAB' : A ≤ B := by linarith
  let a := Nat.floor (A*(N:ℝ))
  let b := Nat.floor (B*(N:ℝ))
  have haLo : (a:ℝ) ≤ A*(N:ℝ) := Nat.floor_le (mul_nonneg hA0 hNp.le)
  have hbLo : (b:ℝ) ≤ B*(N:ℝ) := Nat.floor_le (mul_nonneg hB0 hNp.le)
  have haHi : A*(N:ℝ) < (a:ℝ)+1 := Nat.lt_floor_add_one _
  have hbHi : B*(N:ℝ) < (b:ℝ)+1 := Nat.lt_floor_add_one _
  have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_right hAB' hNp.le)
  have hbN : b ≤ N := Nat.floor_le_of_le (by nlinarith [mul_le_mul_of_nonneg_right hB hNp.le])
  have hAm := mul_le_mul_of_nonneg_right hA hNp.le
  have hABm := mul_le_mul_of_nonneg_right hAB hNp.le
  have hBm := mul_le_mul_of_nonneg_right hB hNp.le
  have hBAm := mul_le_mul_of_nonneg_right hBA hNp.le
  refine ⟨hab,hbN,?_,?_,?_,?_⟩
  · nlinarith
  · rw [Nat.cast_sub hab]
    nlinarith
  · rw [Nat.cast_sub hbN]
    nlinarith
  · nlinarith

end Falconer

end OAI
