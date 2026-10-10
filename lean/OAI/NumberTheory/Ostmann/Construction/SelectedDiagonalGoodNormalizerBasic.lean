import OAI.NumberTheory.Ostmann.Construction.DiagonalFixedOverhead

namespace OAI

open Erdos970

noncomputable section
open Filter
namespace Ostmann.Construction
open Conclusion DiagonalPermutationCount Arithmetic.HistoryProductWindows

def selectedDiagonalGoodRate (k : ℕ) : ℝ :=
  (35+Real.log ((2:ℝ)^k*bulkScale k))*(2:ℝ)^k

lemma bulkScale_one_le {k : ℕ} (hk : 0<k) : 1≤bulkScale k := by
  unfold bulkScale
  exact one_le_pow₀ (by exact_mod_cast (show 1≤k by omega))

lemma selectedDiagonalGoodRate_pos {k : ℕ} (hk : 0<k) :
    0<selectedDiagonalGoodRate k := by
  have hh : 1≤(2:ℝ)^k*bulkScale k :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (bulkScale_one_le hk)
  have hlog := Real.log_nonneg hh
  unfold selectedDiagonalGoodRate
  positivity

lemma stepGap_nonneg_of_budgets {k : ℕ} (hk : 0<k)
    {BD Bz : ℝ} (hD : 0≤BD) (hz : 0≤Bz) (L : ℝ) (l : ℕ) :
    0 ≤ stepGap BD Bz k L l := by
  have hlog := Real.log_nonneg (bulkScale_one_le hk)
  have hrlog := Real.log_nonneg (one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=l))
  unfold stepGap
  positivity

lemma selectedDiagonalGoodRate_dominates {k l : ℕ} (hk : 0<k) (hl : l≤k)
    (m : ℕ) :
    (35+Real.log ((2:ℝ)^l*bulkScale k))*((2:ℝ)^l*m)≤
      selectedDiagonalGoodRate k*m := by
  have hz : 0<bulkScale k := lt_of_lt_of_le zero_lt_one (bulkScale_one_le hk)
  have hr : (2:ℝ)^l≤2^k := pow_le_pow_right₀ (by norm_num) hl
  have hlog : Real.log ((2:ℝ)^l*bulkScale k)≤Real.log ((2:ℝ)^k*bulkScale k) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hr hz.le)
  have hlog0 := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=l))
      (bulkScale_one_le hk))
  have h := mul_le_mul
    (show 35+Real.log ((2:ℝ)^l*bulkScale k)≤35+Real.log ((2:ℝ)^k*bulkScale k) by linarith)
    hr (by positivity)
    (show 0≤35+Real.log ((2:ℝ)^k*bulkScale k) by linarith)
  simpa only [selectedDiagonalGoodRate,mul_assoc] using
    mul_le_mul_of_nonneg_right h (Nat.cast_nonneg m)

theorem remaining_nonbulk_factorial_absorbed_eventually {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀l≤k,
      (((remainingTemplate (bulkSize k L) k l).length+1-2^l*bulkSize k L).factorial:ℝ)≤
        Real.exp ((2:ℝ)^l*(bulkSize k L:ℝ)) := by
  filter_upwards [diagonal_fixed_overhead_absorbed_eventually hk] with L h
  intro l hl
  have hr : (1:ℝ)≤((2^l:ℕ):ℝ) := by
    exact_mod_cast (one_le_pow₀ (by norm_num : (1:ℕ)≤2) (n:=l))
  have hp : (1:ℝ)≤((2^l:ℕ):ℝ)^(2*(2^l)) := one_le_pow₀ hr
  have hw : 0≤nominalInheritedWidth k l+nominalRemovedWidth k l := by
    unfold nominalInheritedWidth nominalRemovedWidth
    positivity
  have he : (1:ℝ)≤Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l) :=
    Real.one_le_exp_iff.mpr hw
  refine le_trans ?_ (h l hl)
  unfold diagonalMatchingOverhead
  exact le_trans (le_mul_of_one_le_right (Nat.cast_nonneg _) hp)
    (le_mul_of_one_le_right (by positivity) he)

end Ostmann.Construction

end

end OAI
