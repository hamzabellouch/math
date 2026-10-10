import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace OAI

/-! # An endpoint-continuous modular strip kernel

The extra factor `s (1-s)^2` makes both boundary functions continuous on
the closed resolvent spectrum. It will cancel on a dense operator range.
-/

namespace KadisonKastler

open Set

noncomputable section

def weightedStripKernel (z : ℂ) (s : ℝ) : ℂ :=
  (s : ℂ) ^ ((3 / 2 : ℂ) - z) * ((1 - s : ℝ) : ℂ) ^ ((5 / 2 : ℂ) + z)

private theorem weighted_exponents_pos {z : ℂ} (hz : |z.re| < 1) :
    0 < ((3 / 2 : ℂ) - z).re ∧ 0 < ((5 / 2 : ℂ) + z).re := by
  have h := abs_lt.mp hz
  constructor <;> norm_num <;> linarith

theorem weightedStripKernel_continuousAt {z : ℂ} {s : ℝ} (hz : |z.re| < 1) :
    ContinuousAt (fun p : ℂ × ℝ => weightedStripKernel p.1 p.2) (z, s) := by
  obtain ⟨h₁, h₂⟩ := weighted_exponents_pos hz
  have ha : ContinuousAt (fun p : ℂ × ℝ => (p.2 : ℂ) ^ ((3 / 2 : ℂ) - p.1)) (z, s) :=
    (Complex.continuousAt_ofReal_cpow s ((3 / 2 : ℂ) - z) (Or.inl h₁)).comp_of_eq
    (by fun_prop : ContinuousAt (fun p : ℂ × ℝ => (p.2, (3 / 2 : ℂ) - p.1)) (z, s)) rfl
  have hb : ContinuousAt (fun p : ℂ × ℝ => ((1 - p.2 : ℝ) : ℂ) ^ ((5 / 2 : ℂ) + p.1)) (z, s) :=
    (Complex.continuousAt_ofReal_cpow (1 - s) ((5 / 2 : ℂ) + z) (Or.inl h₂)).comp_of_eq
    (by fun_prop : ContinuousAt (fun p : ℂ × ℝ => (1 - p.2, (5 / 2 : ℂ) + p.1)) (z, s)) rfl
  exact ha.mul hb

theorem weightedStripKernel_differentiableAt (s : ℝ) {z : ℂ} (hz : |z.re| < 1) :
    DifferentiableAt ℂ (fun z => weightedStripKernel z s) z := by
  obtain ⟨h₁, h₂⟩ := weighted_exponents_pos hz
  have hd₁ : DifferentiableAt ℂ (fun w : ℂ => (3 / 2 : ℂ) - w) z := by fun_prop
  have hd₂ : DifferentiableAt ℂ (fun w : ℂ => (5 / 2 : ℂ) + w) z := by fun_prop
  apply DifferentiableAt.mul
  · exact hd₁.const_cpow
      (Or.inr (ne_of_apply_ne Complex.re h₁.ne'))
  · exact hd₂.const_cpow
      (Or.inr (ne_of_apply_ne Complex.re h₂.ne'))

theorem weightedStripKernel_norm_le_one {z : ℂ} {s : ℝ}
    (hz : |z.re| ≤ 1 / 2) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖weightedStripKernel z s‖ ≤ 1 := by
  have hh := abs_le.mp hz
  have he₁ : 0 < ((3 / 2 : ℂ) - z).re := by norm_num; linarith
  have he₂ : 0 < ((5 / 2 : ℂ) + z).re := by norm_num; linarith
  unfold weightedStripKernel
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_nonneg hs he₁.ne',
    Complex.norm_cpow_eq_rpow_re_of_nonneg (sub_nonneg.mpr hs1) he₂.ne']
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (Real.rpow_le_one hs hs1 he₁.le)
      (Real.rpow_le_one (sub_nonneg.mpr hs1) (by linarith) he₂.le)
      (Real.rpow_nonneg (sub_nonneg.mpr hs1) _) zero_le_one
    _ = 1 := one_mul _

end

end KadisonKastler

end OAI
