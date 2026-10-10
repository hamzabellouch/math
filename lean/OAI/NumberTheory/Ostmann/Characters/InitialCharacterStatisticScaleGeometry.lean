import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.InitialCharacterScale
open Filter

theorem repeated_period_small_eventually {α : ℝ} (hα : 0 < α)
    (BD D : ℝ) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ X : ℝ, 0 < X →
      X*Real.exp (initialGap BD k L+D) < 4*X*Real.exp (Real.exp (α*L)) := by
  let C := |BD+20*Real.log (depthScale k)| * depthScale k+|D|+1
  have hdom := (tendsto_exp_mul_div_rpow_atTop 1 α hα).eventually_gt_atTop C
  filter_upwards [hdom,eventually_ge_atTop (1 : ℝ)] with L hdom hL
  intro X hX
  have hLpos : 0 < L := by linarith
  have hm := (wordSize_bounds k hLpos.le).2
  have hgap : initialGap BD k L+D ≤ C*L := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self (BD+20*Real.log (depthScale k)))
      (Nat.cast_nonneg (α := ℝ) (wordSize k L))
    have h2 := mul_le_mul_of_nonneg_left hm (abs_nonneg (BD+20*Real.log (depthScale k)))
    have h3 := mul_le_mul_of_nonneg_left hL (abs_nonneg D)
    dsimp only [C, initialGap]
    nlinarith [le_abs_self D]
  have hbound : C*L < Real.exp (α*L) := by
    simp only [Real.rpow_one] at hdom
    exact (lt_div_iff₀ hLpos).mp hdom
  have hexp := Real.exp_lt_exp.mpr (hgap.trans_lt hbound)
  calc
    _ < X*Real.exp (Real.exp (α*L)) := mul_lt_mul_of_pos_left hexp hX
    _ ≤ _ := by nlinarith [mul_pos hX (Real.exp_pos (Real.exp (α*L)))]

end Ostmann.Characters.InitialCharacterScale

end

end OAI
