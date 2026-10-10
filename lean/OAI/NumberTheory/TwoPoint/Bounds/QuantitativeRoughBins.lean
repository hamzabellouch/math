import OAI.NumberTheory.TwoPoint.Bounds.RoughLiouvilleShifts
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeRoughBins

namespace OAI

/-! The quantitative rough-shift estimate on the actual logarithmic
bins, retaining the absolute long-interval exponent 1000. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem quantitative_rough_real_bin (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) (h : ℕ) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Y l : ℕ), Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ (Y : ℝ) →
      ∀ [NeZero l] (a : ZMod l) (M τ : ℝ), 0 < τ → τ < 2 →
      ∀ Z : Finset ℕ,
      (∀ z ∈ Z, M ≤ (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        Real.exp (L ^ (199 / 200 : ℝ)) ≤ (z : ℝ) ∧ (z : ℝ) ≤ Real.exp (2 * L) ∧
        avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) →
      ‖roughShiftAverage (progressionSequence liouville l a) liouville Z h Y‖ ≤
        C * L ^ (-21 / 20 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := rough_liouville_shifts hM hMRT h hh
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro Y l hY _ a M τ hτ hτtwo Z hZ
  by_cases hz : Z.Nonempty
  · obtain ⟨z, hz⟩ := hz
    have hzdata := hZ z hz
    have hzm : 0 < τ * M := (Real.exp_pos _).trans_le (hzdata.2.2.1.trans hzdata.2.1)
    have hMpos : 0 < M := by
      rcases mul_pos_iff.mp hzm with hpos | hneg
      · exact hpos.2
      · linarith [hneg.1]
    have hceil : (Nat.ceil M : ℝ) ≤ z := by exact_mod_cast Nat.ceil_le.mpr hzdata.1
    have hlow : (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ Nat.ceil M := by
      have hMc : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
      nlinarith [hzdata.2.1, hzdata.2.2.1]
    have hupp : (Nat.ceil M : ℝ) ≤ Real.exp (2 * L) := hceil.trans hzdata.2.2.2.1
    apply hb Y (Nat.ceil M) l hlow hupp hY a Z
    intro z hz
    have hzD : Nat.ceil M ≤ z := Nat.ceil_le.mpr (hZ z hz).1
    have hMceil : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
    have hzupper : (z : ℝ) < 2 * (Nat.ceil M : ℝ) := by
      nlinarith [(hZ z hz).2.1]
    have hzupperNat : z < Nat.ceil M + Nat.ceil M := by
      have ht : z < 2 * Nat.ceil M := by exact_mod_cast hzupper
      omega
    exact ⟨hzD, hzupperNat, (hZ z hz).2.2.2.2⟩
  · have he : Z = ∅ := not_nonempty_iff_eq_empty.mp hz
    subst Z
    simp only [roughShiftAverage, roughShiftProfile, sum_empty, positivePrefix, sum_const_zero,
      zero_div, norm_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hL) _)

end TwoPointCorrelations

end OAI
