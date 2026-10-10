import OAI.NumberTheory.Ostmann.QuadraticCenter.FrequencySymmetry
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothed

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped ComplexConjugate

theorem quadraticFourierFrequency_summable (q d : ℕ) [NeZero d]
    (G : ZMod d → ℂ) (hG : ∀ x, ‖G x‖ ≤ 1)
    (mInv : ZMod d) (a : ℝ) {R : ℝ} (hR : 0 < R) :
    Summable (quadraticFourierFrequency q d G mInv a R) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  have hs := (Ostmann.QuadraticSieve.schwartz_summable_scaled cutoffFourier
    (R * d) (mul_pos hR hd).ne').norm
  apply (hs.mul_left (Real.sqrt d)).of_norm_bounded
  intro u
  have hJ : ‖(jacobiSym u q : ℂ)‖ ≤ 1 := by
    rcases jacobiSym.trichotomy u q with h | h | h <;> simp [h]
  simp only [quadraticFourierFrequency, norm_mul, weylPhase_norm, mul_one]
  calc
    _ ≤ 1 * Real.sqrt d * ‖cutoffFourier ((u : ℝ) / (R * d))‖ := by
      gcongr
      exact norm_unitaryDFT_le_sqrt G hG _
    _ = _ := by ring

theorem norm_tsum_le_two_positive {f : ℤ → ℂ} (hf : Summable f)
    (hzero : f 0 = 0) {ε : ℂ} (hε : ‖ε‖ ≤ 1)
    (hneg : ∀ u : ℤ, f (-u) = ε * conj (f u)) :
    ‖∑' u : ℤ, f u‖ ≤ 2 * ‖∑' n : ℕ, f ((n : ℤ) + 1)‖ := by
  have hp : Summable (fun n : ℕ => f ((n : ℤ) + 1)) := by
    apply hf.comp_injective
    intro m n h
    exact_mod_cast (add_right_cancel h)
  have hn : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by
    apply hf.comp_injective
    intro m n h
    exact_mod_cast (add_right_cancel (neg_injective h))
  rw [tsum_of_add_one_of_neg_add_one hp hn, hzero, add_zero]
  simp_rw [hneg]
  rw [tsum_mul_left, ← Complex.conj_tsum]
  calc
    _ ≤ ‖∑' n : ℕ, f ((n : ℤ) + 1)‖ +
        ‖ε * conj (∑' n : ℕ, f ((n : ℤ) + 1))‖ := norm_add_le _ _
    _ ≤ ‖∑' n : ℕ, f ((n : ℤ) + 1)‖ +
        1 * ‖∑' n : ℕ, f ((n : ℤ) + 1)‖ := by
      rw [norm_mul, Complex.norm_conj]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hε (norm_nonneg _))
    _ = _ := by ring

theorem quadraticFourierFrequency_two_positive (q d : ℕ) [NeZero d]
    (hq : 1 < q) (G : ZMod d → ℂ) (hG : ∀ x, ‖G x‖ ≤ 1)
    (hreal : ∀ x, conj (G x) = G x) (mInv : ZMod d) (a : ℝ) {R : ℝ} (hR : 0 < R) :
    ‖∑' u : ℤ, quadraticFourierFrequency q d G mInv a R u‖ ≤
      2 * ‖∑' n : ℕ, quadraticFourierFrequency q d G mInv a R ((n : ℤ) + 1)‖ := by
  apply norm_tsum_le_two_positive (ε := (jacobiSym (-1) q : ℂ)) (quadraticFourierFrequency_summable q d G hG mInv a hR)
  · simp only [quadraticFourierFrequency, jacobiSym.zero_left hq, Int.cast_zero, zero_mul]
  · rcases jacobiSym.trichotomy (-1) q with h | h | h <;> simp [h]
  · exact quadraticFourierFrequency_neg q d G hreal mInv a R

end Ostmann.QuadraticCenter

end

end OAI
