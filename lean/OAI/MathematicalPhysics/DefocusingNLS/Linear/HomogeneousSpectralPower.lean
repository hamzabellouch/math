import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! # Geometric power decay from the spectral radius

This quantitative form of Gelfand's formula is used for the restricted
time-step operator after its exceptional spectral subspace is removed.
-/

open Filter Topology

namespace DefocusingNLS

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem operator_powers_le_geometric (T : E →L[ℂ] E) (r : ℝ) (hr : 0 < r)
    (hρ : spectralRadius ℂ T < ENNReal.ofReal r) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ‖T ^ n‖ ≤ C * r ^ n := by
  have hsmall := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius T).eventually
    (gt_mem_nhds hρ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  let M := max N 1
  have hlarge (n : ℕ) (hn : M ≤ n) : ‖T ^ n‖ ≤ r ^ n := by
    have hn0 : n ≠ 0 := by dsimp only [M] at hn; omega
    have hroot : ‖T ^ n‖ ^ (1 / (n : ℝ)) < r :=
      (ENNReal.ofReal_lt_ofReal_iff hr).mp (hN n ((le_max_left N 1).trans hn))
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg (T ^ n)) _)
      hroot.le n
    simpa only [one_div, Real.rpow_inv_natCast_pow (norm_nonneg (T ^ n)) hn0] using hp
  let C := 1 + ∑ i ∈ Finset.range M, ‖T ^ i‖ / r ^ i
  have hsum : 0 ≤ ∑ i ∈ Finset.range M, ‖T ^ i‖ / r ^ i := by positivity
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, fun n => ?_⟩
  by_cases hn : M ≤ n
  · exact (hlarge n hn).trans (le_mul_of_one_le_left (pow_nonneg hr.le n) hC)
  · have hterm : ‖T ^ n‖ / r ^ n ≤ ∑ i ∈ Finset.range M, ‖T ^ i‖ / r ^ i := by
      apply Finset.single_le_sum (s := Finset.range M)
        (f := fun i : ℕ => ‖T ^ i‖ / r ^ i)
      · intro i _
        exact div_nonneg (norm_nonneg _) (pow_nonneg hr.le i)
      · exact Finset.mem_range.mpr (lt_of_not_ge hn)
    apply (div_le_iff₀ (pow_pos hr n)).mp
    exact hterm.trans (by dsimp only [C]; linarith)

theorem operator_powers_decay_of_spectralRadius_lt_one (T : E →L[ℂ] E)
    (hρ : spectralRadius ℂ T < 1) :
    ∃ r C : ℝ, 0 < r ∧ r < 1 ∧ 1 ≤ C ∧ ∀ n : ℕ, ‖T ^ n‖ ≤ C * r ^ n := by
  have hfin : spectralRadius ℂ T ≠ ⊤ := ne_top_of_lt (hρ.trans_le le_top)
  have hrho : (spectralRadius ℂ T).toReal < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hρ
  let r := ((spectralRadius ℂ T).toReal + 1) / 2
  have hr : 0 < r := by
    have hnonneg := ENNReal.toReal_nonneg (a := spectralRadius ℂ T)
    dsimp only [r]
    linarith
  have hr1 : r < 1 := by dsimp only [r]; linarith
  have hρr : spectralRadius ℂ T < ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal hfin, ENNReal.ofReal_lt_ofReal_iff hr]
    dsimp only [r]
    linarith
  obtain ⟨C, hC, hb⟩ := operator_powers_le_geometric T r hr hρr
  exact ⟨r, C, hr, hr1, hC, hb⟩

end

end DefocusingNLS

end OAI
