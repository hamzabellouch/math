import OAI.MeasureTheory.Falconer.Recursion.LocalProfileRegularity
import OAI.MeasureTheory.Falconer.Estimates.DyadicSecantError

namespace OAI

/-! Normalized chord errors give the exact unnormalized profile increments
used in finite nonconcentration and covering estimates. -/
namespace Falconer
open Set

theorem scaled_intervalSecantError (g : ℝ → ℝ) {N : ℝ} (hN : N ≠ 0)
    (a b x : ℝ) :
    N*intervalSecantError (fun t => g (N*t)) (a/N) ((b-a)/N) (x/N) =
      N*(g x-g a)-intervalSecantSlope (fun t => g (N*t)) (a/N) ((b-a)/N)*(x-a) := by
  unfold intervalSecantError
  dsimp only
  rw [mul_div_cancel₀ _ hN,mul_div_cancel₀ _ hN]
  field_simp

theorem normalized_chord_lower (g : ℝ → ℝ) {N : ℝ} (hN : 0 < N)
    {a b x s ε : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hs : s ≤ intervalSecantSlope (fun t => g (N*t)) (a/N) ((b-a)/N))
    (herr : ∀ t ∈ Icc (a/N) (b/N), -ε*((b-a)/N) ≤
      intervalSecantError (fun u => g (N*u)) (a/N) ((b-a)/N) t) :
    s*(x-a)-ε*(b-a) ≤ N*(g x-g a) := by
  have hx' : x/N ∈ Icc (a/N) (b/N) :=
    ⟨(div_le_div_iff_of_pos_right hN).2 hx.1,(div_le_div_iff_of_pos_right hN).2 hx.2⟩
  have he := mul_le_mul_of_nonneg_left (herr _ hx') hN.le
  rw [scaled_intervalSecantError g hN.ne'] at he
  have hcancel : N*(-ε*((b-a)/N)) = -ε*(b-a) := by field_simp
  rw [hcancel] at he
  have hm := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hx.1)
  linarith

theorem normalized_chord_upper (g : ℝ → ℝ) {N : ℝ} (hN : 0 < N)
    {a b x s ε : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hs : intervalSecantSlope (fun t => g (N*t)) (a/N) ((b-a)/N) ≤ s)
    (herr : ∀ t ∈ Icc (a/N) (b/N),
      intervalSecantError (fun u => g (N*u)) (a/N) ((b-a)/N) t ≤ ε*((b-a)/N)) :
    N*(g x-g a) ≤ s*(x-a)+ε*(b-a) := by
  have hx' : x/N ∈ Icc (a/N) (b/N) :=
    ⟨(div_le_div_iff_of_pos_right hN).2 hx.1,(div_le_div_iff_of_pos_right hN).2 hx.2⟩
  have he := mul_le_mul_of_nonneg_left (herr _ hx') hN.le
  rw [scaled_intervalSecantError g hN.ne'] at he
  have hcancel : N*(ε*((b-a)/N)) = ε*(b-a) := by field_simp
  rw [hcancel] at he
  have hm := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hx.1)
  linarith

end Falconer

end OAI
