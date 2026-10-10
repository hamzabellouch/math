import OAI.NumberTheory.Ostmann.QuadraticCenter.FrequencySymmetry
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequency
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticCorrelationExpansion

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def positiveFrequencyAmplitude (d : ℕ) [NeZero d] (G : ZMod d → ℂ)
    (mInv : ZMod d) (a R : ℝ) (u : ℕ) : ℂ :=
  Supply.unitaryDFT G (-((u : ℕ) : ZMod d) * mInv) *
    weylPhase (a * (u : ℝ) / d) * cutoffFourier ((u : ℝ) / (R*d))

theorem quadraticFourierFrequency_nat (q d : ℕ) [NeZero d] (G : ZMod d → ℂ)
    (mInv : ZMod d) (a R : ℝ) (u : ℕ) :
    quadraticFourierFrequency q d G mInv a R (u : ℤ) =
      (jacobiSym (u : ℤ) q : ℂ) * positiveFrequencyAmplitude d G mInv a R u := by
  simp only [quadraticFourierFrequency, positiveFrequencyAmplitude, Int.cast_natCast]
  ring

theorem positiveFrequencyAmplitude_eq_zero {d : ℕ} [NeZero d] (G : ZMod d → ℂ)
    (mInv : ZMod d) (a : ℝ) {R : ℝ} (hR : 0 < R) {u : ℕ} (hu : R*d ≤ (u : ℝ)) :
    positiveFrequencyAmplitude d G mInv a R u = 0 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  have hc : cutoffFourier ((u : ℝ)/(R*d)) = 0 := by
    apply SchwartzCutoff.fourier_psi_zero_of_abs_ge
    rw [abs_of_nonneg (by positivity)]
    exact (le_div_iff₀ (mul_pos hR hd)).mpr (by nlinarith [mul_pos hR hd])
  simp only [positiveFrequencyAmplitude, hc, mul_zero]

theorem quadraticFourierFrequency_positive_finite (q d : ℕ) [NeZero d]
    (G : ZMod d → ℂ) (mInv : ZMod d) (a : ℝ) {R : ℝ} (hR : 0 < R)
    (B : ℕ) (hB : R*d ≤ (B : ℝ)) :
    (∑' n : ℕ, quadraticFourierFrequency q d G mInv a R ((n : ℤ)+1)) =
      ∑ u ∈ Finset.Icc 1 B, (jacobiSym (u : ℤ) q : ℂ) * positiveFrequencyAmplitude d G mInv a R u := by
  have hterm (n : ℕ) : quadraticFourierFrequency q d G mInv a R ((n : ℤ)+1) =
      (jacobiSym ((n+1 : ℕ) : ℤ) q : ℂ) * positiveFrequencyAmplitude d G mInv a R (n+1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using quadraticFourierFrequency_nat q d G mInv a R (n+1)
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range B) (fun n hn => ?_)]
  · apply Finset.sum_bij (fun n _ => n+1)
    · intro n hn
      exact Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hn; omega⟩
    · intro n hn m hm hnm
      omega
    · intro u hu
      obtain ⟨hu1, huB⟩ := Finset.mem_Icc.mp hu
      refine ⟨u-1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro n hn
      rfl
  · have hnB : B ≤ n := Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
    have hn' : R*d ≤ ((n+1 : ℕ) : ℝ) := hB.trans (by exact_mod_cast hnB.trans (Nat.le_succ n))
    rw [positiveFrequencyAmplitude_eq_zero G mInv a hR hn', mul_zero]

end Ostmann.QuadraticCenter

end

end OAI
