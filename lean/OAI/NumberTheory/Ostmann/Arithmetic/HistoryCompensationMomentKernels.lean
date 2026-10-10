import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairPolynomialKernel

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryCompensationMoment
open Construction HistoryPairRepresentatives HistoryPairPolynomialKernel

theorem unitKernel_le_two_div_prime {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) : unitKernel h k hs ks r ≤ 2 * (prime h k r : ℝ)⁻¹ := by
  have hp := representative_prime h k hs ks r
  have hp1 : 1 ≤ prime h k r := hp.one_lt.le
  have hpR : (2 : ℝ) ≤ (prime h k r : ℝ) := by exact_mod_cast hp.two_le
  have hpred : ((prime h k r - 1 : ℕ) : ℝ) = (prime h k r : ℝ) - 1 := by
    simp only [Nat.cast_sub hp1, Nat.cast_one]
  apply (unitKernel_bounds h k hs ks r).2.trans
  rw [hpred]
  have hpos : 0 < (prime h k r : ℝ) := by linarith
  have hpredpos : 0 < (prime h k r : ℝ) - 1 := by linarith
  have hh : 1 / ((prime h k r : ℝ) - 1) ≤ 2 / (prime h k r : ℝ) :=
    (div_le_div_iff₀ hpredpos hpos).mpr (by nlinarith)
  simpa only [one_div, div_eq_mul_inv, one_mul] using hh

theorem mixedKernel_le_two_div_prime {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) : mixedKernel h k hs ks r ≤ 2 * (prime h k r : ℝ)⁻¹ := by
  apply (mixedKernel_bounds h k hs ks r).2.trans
  have hp : 0 ≤ (prime h k r : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  linarith

end Ostmann.Arithmetic.HistoryCompensationMoment

end

end OAI
