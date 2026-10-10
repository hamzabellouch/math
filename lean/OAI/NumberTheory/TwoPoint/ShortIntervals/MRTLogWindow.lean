import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPlancherel
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowIdentity

namespace OAI

/-! The exact finite logarithmic window and its Fourier multiplier. -/

namespace TwoPointCorrelations

open Complex MeasureTheory FourierTransform Set
open scoped ENNReal

noncomputable def mrtLogWindowAtom (b a y : ℝ) : ℂ :=
  (Ico (b - a) b).indicator (fun y => (Real.exp (-y) : ℂ)) y

noncomputable def mrtWindowMultiplier (a t : ℝ) : ℂ :=
  (Complex.exp (((1 : ℂ) + (t : ℂ) * I) * a) - 1) / ((1 : ℂ) + (t : ℂ) * I)

lemma mrtLogWindowAtom_memLp (b a : ℝ) (p : ℝ≥0∞) :
    MemLp (mrtLogWindowAtom b a) p := by
  have hs : volume (Ico (b - a) b) ≠ ⊤ :=
    ne_of_lt ((measure_mono Ico_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top)
  have hh := memLp_indicator_const p measurableSet_Ico (Real.exp (a - b)) (Or.inr hs)
  apply hh.mono'
  · exact (Continuous.aestronglyMeasurable (by fun_prop :
      Continuous (fun y : ℝ => (Real.exp (-y) : ℂ)))).indicator measurableSet_Ico
  · filter_upwards with y
    by_cases hy : y ∈ Ico (b - a) b
    · simp only [mrtLogWindowAtom, indicator_of_mem hy, norm_real, Real.norm_eq_abs,
        Real.abs_exp]
      exact Real.exp_le_exp.mpr (by linarith [hy.1])
    · simp [mrtLogWindowAtom, hy]

lemma mrtLogWindowAtom_integrable (b a : ℝ) : Integrable (mrtLogWindowAtom b a) :=
  (memLp_one_iff_integrable).mp (mrtLogWindowAtom_memLp b a 1)

lemma mrt_one_add_imaginary_ne_zero (t : ℝ) : (1 : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp at hh

theorem mrt_log_window_fourier (b : ℝ) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    𝓕 (mrtLogWindowAtom b a) t =
      Complex.exp (-((1 : ℂ) + (2 * Real.pi * t : ℝ) * I) * b) *
        mrtWindowMultiplier a (2 * Real.pi * t) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  let d : ℂ := 1 + (2 * Real.pi * t : ℝ) * I
  have hd : d ≠ 0 := mrt_one_add_imaginary_ne_zero _
  have he : (fun y : ℝ =>
      Complex.exp ((-2 * Real.pi * y * t : ℝ) * I) • mrtLogWindowAtom b a y) =
      (Ico (b - a) b).indicator (fun y => Complex.exp (-d * y)) := by
    funext y
    by_cases hy : y ∈ Ico (b - a) b
    · simp only [mrtLogWindowAtom, indicator_of_mem hy, smul_eq_mul,
        Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      dsimp [d]
      push_cast
      ring
    · simp [mrtLogWindowAtom, hy]
  rw [he, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show b - a ≤ b by linarith),
    integral_exp_mul_complex (neg_ne_zero.mpr hd)]
  have hex : -d * ((b - a : ℝ) : ℂ) = -d * b + d * a := by push_cast; ring
  rw [hex, Complex.exp_add]
  change (Complex.exp (-d * b) - Complex.exp (-d * b) * Complex.exp (d * a)) / -d =
    Complex.exp (-d * b) * ((Complex.exp (d * a) - 1) / d)
  field_simp
  ring

lemma mrt_log_window_membership {n : ℕ} (hn : 0 < n) (a y : ℝ) :
    y ∈ Ico (Real.log (n : ℝ) - a) (Real.log (n : ℝ)) ↔
      Real.exp y < n ∧ (n : ℝ) ≤ Real.exp a * Real.exp y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hhi : Real.exp y < n ↔ y < Real.log (n : ℝ) := by
    nth_rewrite 1 [← Real.exp_log hn0]
    exact Real.exp_lt_exp
  have hlo : (n : ℝ) ≤ Real.exp a * Real.exp y ↔ Real.log (n : ℝ) - a ≤ y := by
    rw [← Real.exp_add]
    nth_rewrite 1 [← Real.exp_log hn0]
    rw [Real.exp_le_exp]
    constructor <;> intro h <;> linarith
  simp only [mem_Ico, hhi, hlo, and_comm]

noncomputable def mrtLogWindow (S : Finset ℕ) (a : ℕ → ℂ) (v y : ℝ) : ℂ :=
  ∑ n ∈ S, a n * mrtLogWindowAtom (Real.log (n : ℝ)) v y

theorem mrt_log_window_interval (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) (v y : ℝ) :
    mrtLogWindow S a v y = (Real.exp (-y) : ℂ) *
      mrtIntervalSum S a (Real.exp y) ((Real.exp v - 1) * Real.exp y) := by
  have he : Real.exp y + (Real.exp v - 1) * Real.exp y = Real.exp v * Real.exp y := by ring
  simp only [mrtLogWindow, mrtIntervalSum, Finset.mul_sum, he]
  apply Finset.sum_congr rfl
  intro n hnS
  have hm := mrt_log_window_membership (hn n hnS) v y
  by_cases hy : y ∈ Ico (Real.log (n : ℝ) - v) (Real.log (n : ℝ))
  · have hi := hm.mp hy
    simp only [mrtLogWindowAtom, indicator_of_mem hy, ite_eq_left hi]
    ring
  · have hi : ¬(Real.exp y < n ∧ (n : ℝ) ≤ Real.exp v * Real.exp y) :=
      fun h => hy (hm.mpr h)
    simp only [mrtLogWindowAtom, indicator_of_notMem hy, ite_eq_right hi, mul_zero]

end TwoPointCorrelations

end OAI
