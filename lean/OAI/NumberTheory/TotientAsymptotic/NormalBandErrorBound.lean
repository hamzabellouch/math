import OAI.NumberTheory.TotientAsymptotic.FordNormalCount

namespace OAI

/-! A uniform finite-dimensional bound for the normal-band counting error. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma normal_band_error_bound {S k : ℕ} {D H : ℝ} {Y : ℕ → ℕ}
    (hD : 0 ≤ D) (hS : 0 ≤ B S) (_hH : 0 ≤ H)
    (hY : ∀ j < k,B (Y j) ≤ H) :
    normalBandError S D k Y ≤
      D*(k:ℝ)*(k+2)+(k:ℝ)*(k+2)^2*Real.sqrt (B S*H) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      ((j+2:ℕ):ℝ) ≤ (k:ℝ)+2 := by
    have hh := Finset.mem_range.mp hj
    exact_mod_cast (show j+2 ≤ k+2 by omega)
  have hsum : (∑ j ∈ Finset.range k,((j+2:ℕ):ℝ)) ≤ (k:ℝ)*(k+2) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k,((k:ℝ)+2) := Finset.sum_le_sum hterm
      _ = _ := by simp; ring
  have herror (j : ℕ) (hj : j ∈ Finset.range k) :
      ((j+2:ℕ):ℝ)*Real.log (j+2)*Real.sqrt (B S*B (Y j)) ≤
      ((k:ℝ)+2)^2*Real.sqrt (B S*H) := by
    have hj0 : (0:ℝ) ≤ (j+2:ℕ) := Nat.cast_nonneg _
    have hlog0 : 0 ≤ Real.log ((j+2:ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ j+2 by omega))
    have hlog : Real.log ((j+2:ℕ):ℝ) ≤ (k:ℝ)+2 := by
      have hh := Real.log_le_sub_one_of_pos (show 0 < ((j+2:ℕ):ℝ) by positivity)
      linarith [hterm j hj]
    have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hY j (Finset.mem_range.mp hj)) hS)
    have hc : ((j+2:ℕ):ℝ)*Real.log ((j+2:ℕ):ℝ) ≤ ((k:ℝ)+2)^2 := by
      nlinarith [hterm j hj]
    simpa only [Nat.cast_add,Nat.cast_ofNat] using mul_le_mul hc hsqrt (Real.sqrt_nonneg _) (sq_nonneg _)
  have hs : (∑ j ∈ Finset.range k,((j+2:ℕ):ℝ)*Real.log (j+2)*Real.sqrt (B S*B (Y j))) ≤
      (k:ℝ)*(k+2)^2*Real.sqrt (B S*H) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k,((k:ℝ)+2)^2*Real.sqrt (B S*H) := Finset.sum_le_sum herror
      _ = _ := by simp; ring
  simpa only [normalBandError,mul_assoc] using add_le_add (mul_le_mul_of_nonneg_left hsum hD) hs

end TotientAsymptotic

end

end OAI
