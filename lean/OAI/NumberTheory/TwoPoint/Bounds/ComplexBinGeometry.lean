import OAI.NumberTheory.TwoPoint.Walks.CanonicalComplexBin
import OAI.NumberTheory.TwoPoint.Bounds.BinCutoffGeometry

namespace OAI

/-! A literal logarithmic bin supplies the integer short range used by five-color orientation. -/

namespace TwoPointCorrelations

noncomputable def logBinStep (h : ℕ) (η : ℝ) (j : ℤ) : ℤ :=
  ⌈(h : ℝ) * Real.exp ((j : ℝ) * η)⌉

lemma logBinStep_pos (h : ℕ) (hh : 0 < h) (η : ℝ) (j : ℤ) :
    0 < logBinStep h η j := by
  apply Int.ceil_pos.mpr
  exact mul_pos (by exact_mod_cast hh) (Real.exp_pos _)

lemma actualPaddingBin_short_shift (h d q : ℕ) (hh : 0 < h) (hd : 0 < d) (hq : 0 < q)
    (η : ℝ) (hη : Real.exp η < 2) (j : ℤ)
    (hb : actualPaddingBin η (Real.log d) j q) :
    logBinStep h η j ≤ (h * q * d : ℕ) ∧
      (h * q * d : ℕ) < 2 * logBinStep h η j := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hlog : Real.log (d * q : ℕ) = Real.log q + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul hdR.ne' hqR.ne']
    ring
  have hp : (0 : ℝ) < (d * q : ℕ) := by exact_mod_cast Nat.mul_pos hd hq
  have hlo : Real.exp ((j : ℝ) * η) ≤ (d * q : ℕ) := by
    rw [← Real.exp_log hp]
    exact Real.exp_le_exp.mpr (by rw [hlog]; exact hb.1)
  have hhi : (d * q : ℕ) < Real.exp ((j : ℝ) * η) * Real.exp η := by
    rw [← Real.exp_add]
    calc
      _ = Real.exp (Real.log (d * q : ℕ)) := (Real.exp_log hp).symm
      _ < _ := Real.exp_lt_exp.mpr (by rw [hlog]; nlinarith [hb.2])
  have hc : (h : ℝ) * Real.exp ((j : ℝ) * η) ≤ (logBinStep h η j : ℝ) :=
    Int.le_ceil _
  constructor
  · apply Int.ceil_le.mpr
    push_cast
    have he := mul_le_mul_of_nonneg_left hlo hhR.le
    push_cast at he
    nlinarith
  · have he := mul_lt_mul_of_pos_left hhi hhR
    have hex := mul_lt_mul_of_pos_left hη (Real.exp_pos ((j : ℝ) * η))
    have hexh := mul_lt_mul_of_pos_left hex hhR
    have hr : ((h * q * d : ℕ) : ℝ) < 2 * (logBinStep h η j : ℝ) := by
      push_cast at he ⊢
      nlinarith
    exact_mod_cast hr

end TwoPointCorrelations

end OAI
