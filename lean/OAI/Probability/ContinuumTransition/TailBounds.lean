import OAI.Probability.ContinuumTransition.ConstructionLocation

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem cubeCells_card_coarse {L : ℝ} (hL : 1 ≤ L) :
    ((cubeCells L).card : ℝ) ≤ 216*L^3 := by
  have h0 : 0 ≤ L := le_trans zero_le_one hL
  have hh : 4*L+2 ≤ 6*L := by linarith only [hL]
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 4*L+2) hh 3
  have hb := card_cubeCells_le h0
  nlinarith only [hp, hb]

theorem physical_small_subpart {t : ℝ} (ht : 0 ≤ t) {σ τ : ℕ → ℝ}
    (hτ : ∀ n, 0 ≤ τ n) (hs : Summable σ) (hτs : Summable τ)
    (hsmall : 2197*t*kernelHeight*(∑' n, (σ n+τ n)) ≤ (t^2/8)/8) :
    2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8 := by
  have hb := hs.tsum_le_tsum (fun n => le_add_of_nonneg_right (hτ n)) (hs.add hτs)
  have hm := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2197) ht) kernelHeight_pos.le)
  nlinarith only [hm, hsmall, sq_nonneg t]

end ContinuumTemperature
end

end OAI
