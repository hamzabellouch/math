import OAI.NumberTheory.JointDickman.Arithmetic.SieveScale

namespace OAI

/-! # The fixed sieve cutoff used for the addition-product small-ball bound -/

namespace JointDickman

open Filter
open scoped Topology

noncomputable def additionSieveCutoff (Y : ℝ) : ℕ := ⌊Real.exp (Y / 100)⌋₊

theorem additionSieveCutoff_eventually :
    ∀ᶠ Y : ℝ in atTop, 0 < Y ∧ 2 ≤ additionSieveCutoff Y ∧
      Y / 200 ≤ Real.log (additionSieveCutoff Y) ∧
      (additionSieveCutoff Y : ℝ) ≤ Real.exp (Y / 100) ∧
      (2 * (additionSieveCutoff Y + 1 : ℝ) * additionSieveCutoff Y) * Y ≤ Real.exp (Y / 2) := by
  have hexp : ∀ᶠ Y : ℝ in atTop, 2 ≤ Real.exp (Y / 200) := by
    apply (Real.tendsto_exp_atTop.comp ?_).eventually_ge_atTop 2
    exact tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 200)
  have hlim : Tendsto (fun Y : ℝ => 4 * (Y / Real.exp ((12 / 25 : ℝ) * Y))) atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0 : ℝ) < 12 / 25)).tendsto_div_nhds_zero
    simpa only [pow_one, mul_zero] using h.const_mul 4
  filter_upwards [hexp, hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 0] with Y he hs hY
  have hfloor : Real.exp (Y / 200) ≤ (additionSieveCutoff Y : ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp (Y / 100))
    change Real.exp (Y / 100) < (additionSieveCutoff Y : ℝ) + 1 at hh
    have heq : Real.exp (Y / 100) = Real.exp (Y / 200)^2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [heq] at hh
    nlinarith only [hh, he]
  have hlog : Y / 200 ≤ Real.log (additionSieveCutoff Y) := by
    have hh := Real.log_le_log (Real.exp_pos (Y / 200)) hfloor
    simpa only [Real.log_exp] using hh
  have hZupper : (additionSieveCutoff Y : ℝ) ≤ Real.exp (Y / 100) := Nat.floor_le (Real.exp_pos _).le
  have hZ0 : (0 : ℝ) ≤ additionSieveCutoff Y := Nat.cast_nonneg _
  have he1 : 1 ≤ Real.exp (Y / 100) := Real.one_le_exp_iff.mpr (by positivity)
  have hrem : 2 * (additionSieveCutoff Y + 1 : ℝ) * additionSieveCutoff Y ≤
      4 * Real.exp (Y / 50) := by
    calc
      _ ≤ 2 * (2 * Real.exp (Y / 100)) * Real.exp (Y / 100) := by gcongr; linarith only [hZupper, he1]
      _ = _ := by rw [show Y / 50 = Y / 100 + Y / 100 by ring, Real.exp_add]; ring
  have hsmall : 4 * Y ≤ Real.exp ((12 / 25 : ℝ) * Y) := by
    apply (div_le_one (Real.exp_pos _)).mp
    convert hs using 1
    ring
  refine ⟨hY, ?_, hlog, hZupper, ?_⟩
  · exact_mod_cast he.trans hfloor
  · calc
      _ ≤ (4 * Real.exp (Y / 50)) * Y := mul_le_mul_of_nonneg_right hrem hY.le
      _ = (4 * Y) * Real.exp (Y / 50) := by ring
      _ ≤ Real.exp ((12 / 25 : ℝ) * Y) * Real.exp (Y / 50) :=
        mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end JointDickman

end OAI
