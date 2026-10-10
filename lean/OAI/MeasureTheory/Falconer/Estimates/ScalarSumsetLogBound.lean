import OAI.MeasureTheory.Falconer.Estimates.ScalarInitialGrowth

namespace OAI

/-! Comparing the original fixed-fold sumset with small doubling. The
 logarithmic loss does not contain the regularization factor. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_sumset_log_bound {δ K : ℝ} (_hδ : 0 < δ) (hK : 0 < K)
    (A : Finset ℝ) (hA : A.Nonempty)
    (hsmall : ((scalarCells δ (A+A)).card:ℝ) ≤ K*(scalarCells δ A).card)
    (copies : ℕ) :
    Real.log ((scalarCells δ (copies • A)).card:ℝ) ≤
      Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log (2*K)+Real.log (A.card:ℝ) := by
  have hp := scalar_pluennecke δ A A hA hsmall copies 0
  simp only [zero_nsmul,sub_zero,add_zero,Nat.cast_zero] at hp
  have hcard : ((scalarCells δ A).card:ℝ) ≤ (A.card:ℝ) := by
    exact_mod_cast Finset.card_image_le (s := A)
  have hu := hp.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
  have hs : (scalarCells δ (copies • A)).Nonempty := (hA.nsmul).image _
  have hpos : (0:ℝ) < ((scalarCells δ (copies • A)).card:ℝ) := by exact_mod_cast hs.card_pos
  have hAc : (0:ℝ) < (A.card:ℝ) := by exact_mod_cast hA.card_pos
  have hl := Real.log_le_log hpos hu
  rw [Real.log_mul (by positivity) hAc.ne',Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at hl
  exact hl

 theorem scalar_weak_prefix_budget {B P M : ℕ} {κ K0 : ℝ} (hκ : 0 ≤ κ)
    (hB : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (hweak : Real.log K0 ≤ κ^2*(B:ℝ)*(M:ℝ)*Real.log 2/160) :
    40*Real.log K0 ≤ (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2 := by
  have hp : (0:ℝ) ≤ (P:ℝ) := Nat.cast_nonneg _
  have hc : κ*(B:ℝ)/4 ≤ κ*(B:ℝ)-2*(P:ℝ) := by linarith
  have hh := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ κ*(M:ℝ)*Real.log 2 by positivity)
  nlinarith

end Falconer

end OAI
