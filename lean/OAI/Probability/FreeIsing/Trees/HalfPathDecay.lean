import Mathlib

namespace OAI

noncomputable section

namespace Problem367.HalfPathDecay

theorem third_le_halves {r : ℕ} (hr : 2 ≤ r) :
    (r : ℝ) / 3 ≤ (r / 2 : ℕ) ∧
      (r : ℝ) / 3 ≤ (r - r / 2 : ℕ) := by
  have hleft : r ≤ 3 * (r / 2) := by omega
  have hright : r ≤ 3 * (r - r / 2) := by omega
  constructor
  · have h : (r : ℝ) ≤ 3 * (r / 2 : ℕ) := by exact_mod_cast hleft
    linarith
  · have h : (r : ℝ) ≤ 3 * (r - r / 2 : ℕ) := by exact_mod_cast hright
    linarith

theorem cutoff_le_halves {r : ℕ} {C ω : ℝ}
    (hr : 2 ≤ r) (_hω : 0 < ω) (hlen : 3 * C / ω ≤ (r : ℝ)) :
    C / ω ≤ (r / 2 : ℕ) ∧ C / ω ≤ (r - r / 2 : ℕ) := by
  have hC : C / ω ≤ (r : ℝ) / 3 := by
    have heq : 3 * C / ω = 3 * (C / ω) := by ring
    rw [heq] at hlen
    linarith
  exact ⟨hC.trans (third_le_halves hr).1, hC.trans (third_le_halves hr).2⟩

theorem two_le_of_cutoff {r : ℕ} {C ω : ℝ}
    (hC : 2 ≤ C) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hlen : C / ω ≤ (r : ℝ)) : 2 ≤ r := by
  have hmul : 2 * ω ≤ C := by linarith
  have hbound : (2 : ℝ) ≤ (r : ℝ) :=
    ((le_div_iff₀ hω).2 hmul).trans hlen
  exact_mod_cast hbound

theorem exponential_le {r n : ℕ} {η ω : ℝ}
    (hη : 0 ≤ η) (hω : 0 ≤ ω) (hlen : (r : ℝ) / 3 ≤ (n : ℝ)) :
    Real.exp (-(η * ω) * n) ≤ Real.exp (-((η / 3) * ω) * r) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hlen (mul_nonneg hη hω)
  nlinarith

theorem twelfth_power_eq {b : ℝ} (hb : 0 ≤ b) (r : ℕ) :
    (b ^ ((1 : ℝ) / 12)) ^ r = b ^ ((r : ℝ) / 12) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
  congr 1
  ring

theorem double_exponential_le {r n : ℕ} {b : ℝ}
    (hb : 1 < b) (hlen : (r : ℝ) / 3 ≤ (n : ℝ)) :
    Real.exp (-(b ^ ((n : ℝ) / 4)) / (2 * b)) ≤
      Real.exp (-(1 / (2 * b)) * (b ^ ((1 : ℝ) / 12)) ^ r) := by
  rw [twelfth_power_eq (zero_le_one.trans hb.le)]
  apply Real.exp_le_exp.mpr
  have hexp : (r : ℝ) / 12 ≤ (n : ℝ) / 4 := by linarith
  have hp := Real.rpow_le_rpow_of_exponent_le hb.le hexp
  have hden : 0 < 2 * b := by positivity
  have hdiv := div_le_div_of_nonneg_right hp hden.le
  calc
    -(b ^ ((n : ℝ) / 4)) / (2 * b) = -(b ^ ((n : ℝ) / 4) / (2 * b)) := by ring
    _ ≤ -(b ^ ((r : ℝ) / 12) / (2 * b)) := neg_le_neg hdiv
    _ = -(1 / (2 * b)) * b ^ ((r : ℝ) / 12) := by ring

theorem measure_gt_le_common_decay {α : Type*} [MeasurableSpace α]
    (ν : MeasureTheory.Measure α) (X : α → ℝ)
    {r n : ℕ} {b η ω K : ℝ} (hb : 1 < b) (hη : 0 ≤ η)
    (hω : 0 ≤ ω) (hK : 0 ≤ K) (hlen : (r : ℝ) / 3 ≤ (n : ℝ))
    (htail : ν {x | K * Real.exp (-(η * ω) * n) ≤ X x} ≤
      ENNReal.ofReal (Real.exp (-(b ^ ((n : ℝ) / 4)) / (2 * b)))) :
    ν {x | K * Real.exp (-((η / 3) * ω) * r) < X x} ≤
      ENNReal.ofReal
        (Real.exp (-(1 / (2 * b)) * (b ^ ((1 : ℝ) / 12)) ^ r)) := by
  refine (MeasureTheory.measure_mono ?_).trans
    (htail.trans (ENNReal.ofReal_le_ofReal (double_exponential_le hb hlen)))
  intro x hx
  exact (mul_le_mul_of_nonneg_left (exponential_le hη hω hlen) hK).trans hx.le

end Problem367.HalfPathDecay

end

end OAI
