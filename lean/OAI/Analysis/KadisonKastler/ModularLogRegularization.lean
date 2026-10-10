import OAI.Analysis.KadisonKastler.RegularizedModularGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! # Uniform weighted bounds for logarithmic regularization

Multiplication by `s(1-s)` removes both endpoint singularities of the
regularized modular logarithm. These estimates give strong convergence
of its exponential on the dense range of `R(1-R)`.
-/

namespace KadisonKastler

noncomputable section

/-- Scalar logarithmic generator at a positive regularization scale. -/
def regularizedLogScalar (ε s : ℝ) : ℝ :=
  Real.log (1 - s + ε) - Real.log (s + ε)

private theorem weighted_log_difference_ordered (s ε δ : ℝ) (hs : 0 ≤ s)
    (hδ : 0 < δ) (hδε : δ ≤ ε) :
    s * (Real.log (s + ε) - Real.log (s + δ)) ≤ ε - δ := by
  have hd : 0 < s + δ := by positivity
  have he : 0 < s + ε := by linarith
  have hlog : 0 ≤ Real.log (s + ε) - Real.log (s + δ) :=
    sub_nonneg.mpr (Real.log_le_log hd (by linarith))
  have h := Real.log_le_sub_one_of_pos (div_pos he hd)
  rw [Real.log_div he.ne' hd.ne'] at h
  have hrat : (s + ε) / (s + δ) - 1 = (ε - δ) / (s + δ) := by
    field_simp
    ring
  rw [hrat] at h
  have hm := (le_div_iff₀ hd).mp h
  nlinarith [mul_nonneg hδ.le hlog]

theorem weighted_log_difference (s ε δ : ℝ) (hs : 0 ≤ s)
    (hε : 0 < ε) (hδ : 0 < δ) :
    s * |Real.log (s + ε) - Real.log (s + δ)| ≤ |ε - δ| := by
  rcases le_total δ ε with h | h
  · have hd : 0 < s + δ := by positivity
    have hl := Real.log_le_log hd (show s + δ ≤ s + ε by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hl), abs_of_nonneg (sub_nonneg.mpr h)]
    exact weighted_log_difference_ordered s ε δ hs hδ h
  · have he : 0 < s + ε := by positivity
    have hl := Real.log_le_log he (show s + ε ≤ s + δ by linarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hl), abs_of_nonpos (sub_nonpos.mpr h), neg_sub, neg_sub]
    exact weighted_log_difference_ordered s δ ε hs hε h

theorem weighted_regularizedLog_difference (s ε δ : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hε : 0 < ε) (hδ : 0 < δ) :
    s * (1 - s) * |regularizedLogScalar ε s - regularizedLogScalar δ s| ≤ |ε - δ| := by
  have hc : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have ha := weighted_log_difference (1 - s) ε δ hc hε hδ
  have hb := weighted_log_difference s ε δ hs hε hδ
  have ht : |regularizedLogScalar ε s - regularizedLogScalar δ s| ≤
      |Real.log (1 - s + ε) - Real.log (1 - s + δ)| +
      |Real.log (s + ε) - Real.log (s + δ)| := by
    have heq : regularizedLogScalar ε s - regularizedLogScalar δ s =
        (Real.log (1 - s + ε) - Real.log (1 - s + δ)) -
        (Real.log (s + ε) - Real.log (s + δ)) := by
      unfold regularizedLogScalar
      ring
    rw [heq]
    exact abs_sub _ _
  calc
    _ ≤ s * (1 - s) *
        (|Real.log (1 - s + ε) - Real.log (1 - s + δ)| +
          |Real.log (s + ε) - Real.log (s + δ)|) :=
      mul_le_mul_of_nonneg_left ht (mul_nonneg hs hc)
    _ = s * ((1 - s) * |Real.log (1 - s + ε) - Real.log (1 - s + δ)|) +
        (1 - s) * (s * |Real.log (s + ε) - Real.log (s + δ)|) := by ring
    _ ≤ s * |ε - δ| + (1 - s) * |ε - δ| :=
      add_le_add (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb hc)
    _ = |ε - δ| := by ring

theorem imaginary_exp_difference (a b : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤ |a - b| := by
  have heq : Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b) =
      Complex.exp (Complex.I * b) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    have harg : Complex.I * (b : ℂ) + Complex.I * ((a - b : ℝ) : ℂ) =
        Complex.I * (a : ℂ) := by
      push_cast
      ring
    rw [harg]
  rw [heq, norm_mul]
  have hn : ‖Complex.exp (Complex.I * b)‖ = 1 := by simp [Complex.norm_exp]
  rw [hn, one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

theorem weighted_modularPhase_difference (t s ε δ : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hε : 0 < ε) (hδ : 0 < δ) :
    s * (1 - s) * ‖Complex.exp (Complex.I * ((t * regularizedLogScalar ε s : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((t * regularizedLogScalar δ s : ℝ) : ℂ))‖ ≤ |t| * |ε - δ| := by
  have hphase := imaginary_exp_difference (t * regularizedLogScalar ε s)
    (t * regularizedLogScalar δ s)
  conv at hphase => rhs; rw [← mul_sub, abs_mul]
  calc
    _ ≤ s * (1 - s) * (|t| * |regularizedLogScalar ε s - regularizedLogScalar δ s|) :=
      mul_le_mul_of_nonneg_left hphase (mul_nonneg hs (sub_nonneg.mpr hs1))
    _ = |t| * (s * (1 - s) * |regularizedLogScalar ε s - regularizedLogScalar δ s|) := by ring
    _ ≤ |t| * |ε - δ| := mul_le_mul_of_nonneg_left
      (weighted_regularizedLog_difference s ε δ hs hs1 hε hδ) (abs_nonneg t)

end

end KadisonKastler

end OAI
