import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.MeanZeroGramDecay
import OAI.Analysis.RieszRectifiability.Kernel.LipschitzTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem lipschitz_amplitude_of_ball_support {d : ℕ} [Nontrivial (Ambient d)]
    (f : Ambient d → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L f)
    (z : Ambient d) (R : ℝ) (hR : 0 < R)
    (hs : tsupport f ⊆ ball z R) (x : Ambient d) :
    |f x| ≤ 2 * (L : ℝ) * R := by
  obtain ⟨v, hv⟩ := exists_norm_eq (E := Ambient d) hR.le
  let y := z + v
  have hy : dist y z = R := by
    dsimp [y]
    rw [dist_eq_norm]
    simpa only [add_sub_cancel_left] using! hv
  have hyzero : f y = 0 := by
    by_contra hn
    have hh := hs (subset_tsupport f hn)
    change dist y z < R at hh
    rw [hy] at hh
    exact (lt_irrefl R) hh
  by_cases hx : f x = 0
  · rw [hx, abs_zero]
    positivity
  have hxR : dist x z < R := hs (subset_tsupport f hx)
  have hxy : dist x y ≤ 2 * R := by
    have ht := dist_triangle x z y
    rw [dist_comm z y, hy] at ht
    linarith
  have hl := hLip.dist_le_mul x y
  rw [Real.dist_eq, hyzero, sub_zero] at hl
  calc
    _ ≤ (L : ℝ) * dist x y := hl
    _ ≤ (L : ℝ) * (2 * R) := mul_le_mul_of_nonneg_left hxy L.coe_nonneg
    _ = _ := by ring

theorem original_oscillation_test_amplitude {d : ℕ} [Nontrivial (Ambient d)]
    (f : Ambient d → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L f)
    (z : Ambient d) (r J : ℝ) (hr : 0 < r) (hJ : 0 < J)
    (hL : (L : ℝ) ≤ 1 / r) (hs : tsupport f ⊆ ball z (J * r))
    (x : Ambient d) : |f x| ≤ 2 * J := by
  calc
    _ ≤ 2 * (L : ℝ) * (J * r) :=
      lipschitz_amplitude_of_ball_support f L hLip z (J * r) (mul_pos hJ hr) hs x
    _ ≤ 2 * (1 / r) * (J * r) := by gcongr
    _ = _ := by field_simp

end

end RieszRectifiability

end OAI
