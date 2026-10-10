import OAI.NumberTheory.JointDickman.Amplification.PublishedInputs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI

/-!
# The nonprincipal-character consequence of the published complex input

The arithmetic proof that the pretentious distance tends to infinity is a
separate obligation. Given exactly that fact, the Matomäki--Radziwiłł--Tao
input proves the short-average conclusion in the order of limits used in
`labels-short`: the main scale tends to infinity before the short length.
-/

namespace JointDickman.PublishedInputs

open Filter MeasureTheory
open scoped Topology

/-- The pretentious-distance error in the published complex estimate. -/
noncomputable def distanceError (M : ℝ) : ℝ := (1 + M) * Real.exp (-M)

/-- The short-length error; it is fixed in the inner scale limit. -/
noncomputable def shortLengthError (H : ℝ) : ℝ :=
  (Real.log (Real.log H) / Real.log H) ^ 2

/-- The long-scale error in the published complex estimate. -/
noncomputable def longScaleError (X : ℝ) : ℝ :=
  (Real.log X) ^ (-(1 : ℝ) / 50)

theorem tendsto_distanceError : Tendsto distanceError atTop (𝓝 0) := by
  change Tendsto (fun M : ℝ => (1 + M) * Real.exp (-M)) atTop (𝓝 0)
  have hzero : Tendsto (fun M : ℝ => Real.exp (-M)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have hone : Tendsto (fun M : ℝ => M * Real.exp (-M)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  simpa [distanceError, add_mul] using hzero.add hone

theorem tendsto_shortLengthError : Tendsto shortLengthError atTop (𝓝 0) := by
  change Tendsto (fun H : ℝ => (Real.log (Real.log H) / Real.log H) ^ 2) atTop (𝓝 0)
  have hlog : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simpa [shortLengthError, Function.comp_def] using
    (hlog.comp Real.tendsto_log_atTop).pow 2

theorem tendsto_longScaleError : Tendsto longScaleError atTop (𝓝 0) := by
  change Tendsto (fun X : ℝ => (Real.log X) ^ (-(1 : ℝ) / 50)) atTop (𝓝 0)
  simpa only [longScaleError, neg_div, Function.comp_def] using
    (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 50) (by norm_num)).comp
      Real.tendsto_log_atTop

/-- If all three parameters tend to infinity along one sequence, the complete
right-hand side of the published complex estimate tends to zero. -/
theorem tendsto_complex_error {M H X : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) (hH : Tendsto H atTop atTop)
    (hX : Tendsto X atTop atTop) (C : ℝ) :
    Tendsto (fun n => C * (distanceError (M n) + shortLengthError (H n) +
      longScaleError (X n))) atTop (𝓝 0) := by
  simpa using (((tendsto_distanceError.comp hM).add
    (tendsto_shortLengthError.comp hH)).add
      (tendsto_longScaleError.comp hX)).const_mul C

/-- The exact iterated upper-limit conclusion for a nonprincipal-character
summand. The sole number-theoretic hypotheses are the explicitly published
complex input and divergence of its specified pretentious distance. -/
theorem complexShortAverage_eventually_eventually (hMRT : ComplexShortIntervalInput)
    (f : ℕ → ℕ → ArithmeticFunction ℂ)
    (hmult : ∀ B n, (f B n).IsMultiplicative)
    (hf : ∀ B n k, ‖f B n k‖ ≤ 1)
    (H : ℕ → ℝ) (X : ℕ → ℕ → ℝ)
    (hH : Tendsto H atTop atTop)
    (hX : ∀ B, Tendsto (X B) atTop atTop)
    (hdistance : ∀ B, Tendsto (fun n => minimumDistance (f B n) (X B n))
      atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1 / X B n) * (∫ z in X B n..2 * X B n,
        ‖complexShortAverage (f B n) (H B) z‖ ^ 2) < ε := by
  obtain ⟨C, _, hbound⟩ := hMRT
  intro ε hε
  have hlarge : ∀ᶠ B in atTop, 10 ≤ H B :=
    hH.eventually (eventually_ge_atTop 10)
  have hshort : ∀ᶠ B in atTop, C * shortLengthError (H B) < ε / 3 := by
    have ht := (tendsto_shortLengthError.comp hH).const_mul C
    exact ht.eventually (gt_mem_nhds (by simpa using div_pos hε (by norm_num : (0 : ℝ) < 3)))
  filter_upwards [hlarge, hshort] with B hB hBshort
  have hlength : ∀ᶠ n in atTop, H B ≤ X B n :=
    (hX B).eventually (eventually_ge_atTop (H B))
  have hdist : ∀ᶠ n in atTop,
      C * distanceError (minimumDistance (f B n) (X B n)) < ε / 3 := by
    have ht := (tendsto_distanceError.comp (hdistance B)).const_mul C
    exact ht.eventually (gt_mem_nhds (by simpa using div_pos hε (by norm_num : (0 : ℝ) < 3)))
  have hlong : ∀ᶠ n in atTop, C * longScaleError (X B n) < ε / 3 := by
    have ht := (tendsto_longScaleError.comp (hX B)).const_mul C
    exact ht.eventually (gt_mem_nhds (by simpa using div_pos hε (by norm_num : (0 : ℝ) < 3)))
  filter_upwards [hlength, hdist, hlong] with n hn hndist hnlong
  have hb := hbound (f B n) (hmult B n) (hf B n) (H B) (X B n) hB hn
  change (1 / X B n) * (∫ z in X B n..2 * X B n,
    ‖complexShortAverage (f B n) (H B) z‖ ^ 2) ≤
      C * (distanceError (minimumDistance (f B n) (X B n)) +
        shortLengthError (H B) + longScaleError (X B n)) at hb
  nlinarith

end JointDickman.PublishedInputs

end OAI
