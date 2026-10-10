import OAI.NumberTheory.TwoPoint.Bounds.WindowPolynomialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Numerical scale estimates for the published MRT short-sum error. -/

namespace TwoPointCorrelations

open Filter

lemma eventually_four_log_le_small_power :
    ∀ᶠ L : ℝ in atTop, 4 * Real.log L ≤ L ^ (39 / 200 : ℝ) := by
  have hh := (isLittleO_log_rpow_atTop
    (show 0 < (39 / 200 : ℝ) by norm_num)).bound (show 0 < (1 / 4 : ℝ) by norm_num)
  filter_upwards [eventually_ge_atTop 1, hh] with L hL h
  have hLp : 0 < L := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL),
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLp _)] at h
  linarith

/-- The two published error terms have the required power saving under
the precise logarithmic consequences of the manuscript scale choices. -/
theorem eventually_mrtShortError_scale :
    ∀ᶠ L : ℝ in atTop, ∀ X D : ℕ,
      (1 / 2 : ℝ) * L ^ (199 / 200 : ℝ) ≤ Real.log D →
      Real.log D ≤ 2 * L → L ^ (560 : ℝ) ≤ Real.log X →
      mrtShortError X D ≤ 2 * L ^ (-4 / 5 : ℝ) := by
  filter_upwards [eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_four_log_le_small_power] with L hL hlog hsmall
  intro X D hDlower hDupper hXlower
  have hLp : 0 < L := by linarith
  have hDlog : 0 < Real.log (D : ℝ) :=
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos hLp _)).trans_le hDlower
  have hloglog : Real.log (Real.log (D : ℝ)) ≤ 2 * Real.log L := by
    have hh := Real.log_le_log hDlog hDupper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hLp.ne'] at hh
    have htwo : Real.log 2 ≤ 1 := by
      have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hfirst : Real.log (Real.log (D : ℝ)) / Real.log D ≤ L ^ (-4 / 5 : ℝ) := by
    calc
      _ ≤ (2 * Real.log L) / Real.log D := div_le_div_of_nonneg_right hloglog hDlog.le
      _ ≤ (2 * Real.log L) / ((1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hDlower
      _ = (4 * Real.log L) / L ^ (199 / 200 : ℝ) := by ring
      _ ≤ L ^ (39 / 200 : ℝ) / L ^ (199 / 200 : ℝ) :=
        div_le_div_of_nonneg_right hsmall (by positivity)
      _ = L ^ (-4 / 5 : ℝ) := by rw [← Real.rpow_sub hLp]; norm_num
  have hsecond : (Real.log (X : ℝ)) ^ (-1 / 700 : ℝ) ≤ L ^ (-4 / 5 : ℝ) := by
    calc
      _ ≤ (L ^ (560 : ℝ)) ^ (-1 / 700 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hLp _) hXlower (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hLp.le]; norm_num
  exact add_le_add hfirst hsecond |>.trans_eq (by ring)

/-- The original exponential cutoff hypotheses imply all logarithmic
conditions above, with no integer-floor or endpoint loss. -/
theorem eventually_mrtShortError_cutoffs :
    ∀ᶠ L : ℝ in atTop, ∀ X D : ℕ,
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (2 * L) →
      Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ X →
      mrtShortError X D ≤ 2 * L ^ (-4 / 5 : ℝ) := by
  have hsmall := (tendsto_rpow_atTop
    (show 0 < (199 / 200 : ℝ) by norm_num)).eventually
      (eventually_ge_atTop (2 * Real.log 2))
  have hlarge := (tendsto_rpow_atTop
    (show 0 < (440 : ℝ) by norm_num)).eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop 1, eventually_mrtShortError_scale, hsmall, hlarge]
    with L hL hscale hs hl
  intro X D hDlower hDupper hXlower
  have hLp : 0 < L := by linarith
  have hDp : (0 : ℝ) < D :=
    (mul_pos (by norm_num) (Real.exp_pos _)).trans_le hDlower
  apply hscale X D
  · have hh := Real.log_le_log (show (0 : ℝ) < (1 / 2 : ℝ) *
        Real.exp (L ^ (199 / 200 : ℝ)) by positivity) hDlower
    rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp] at hh
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [hhalf] at hh
    linarith
  · have hh := Real.log_le_log hDp hDupper
    simpa only [Real.log_exp] using hh
  · have hh := Real.log_le_log (Real.exp_pos _) hXlower
    rw [Real.log_exp] at hh
    have hp : (1 / 2 : ℝ) * L ^ (1000 : ℝ) ≥ L ^ (560 : ℝ) := by
      have he : L ^ (1000 : ℝ) = L ^ (560 : ℝ) * L ^ (440 : ℝ) := by
        rw [← Real.rpow_add hLp]
        norm_num
      rw [he]
      nlinarith [Real.rpow_pos_of_pos hLp (560 : ℝ)]
    exact hp.trans hh

/-- The published short-interval theorem now bounds the actual progression
polynomials on the manuscript scales. The bound is uniform over the circle. -/
theorem MRTLiouvilleShortInput.progression_window_scale (hMRT : MRTLiouvilleShortInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ∀ (Y D l : ℕ),
      1 ≤ Y → 10 ≤ D → D ≤ Y + 1 →
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (2 * L) →
      Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ (Y + 1 : ℕ) →
      ∀ [NeZero l] (a : ZMod l) (θ : AddCircle (1 : ℝ)),
        (∑ v ∈ Finset.range Y,
          ‖forwardWindowPolynomial (progressionSequence liouville l a) D (v + 1) θ‖) ≤
            C * Y * D * L ^ (-4 / 5 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := hMRT.progression_window_polynomials
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [eventually_mrtShortError_cutoffs, eventually_ge_atTop 1]
    with L hscale hL
  intro Y D l hY hD hDY hDlower hDupper hYlower _ a θ
  have he := hscale (Y + 1) D hDlower hDupper hYlower
  have hYr : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hLp : 0 < L := by linarith
  calc
    _ ≤ C * (D : ℝ) * (Y + 1 : ℕ) * mrtShortError (Y + 1) D :=
      hbound Y D l hD hDY a θ
    _ ≤ C * (D : ℝ) * (Y + 1 : ℕ) * (2 * L ^ (-4 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ C * (D : ℝ) * (2 * Y) * (2 * L ^ (-4 / 5 : ℝ)) := by
      have hy : ((Y + 1 : ℕ) : ℝ) ≤ 2 * Y := by push_cast; linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hy (by positivity)) (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
