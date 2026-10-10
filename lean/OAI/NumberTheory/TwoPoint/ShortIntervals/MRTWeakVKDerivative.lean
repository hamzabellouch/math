import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingGrowthWindow
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Uniform high-height logarithmic-derivative consequence of the explicit
weak Hurwitz growth input. The polynomial modulus loss has disappeared:
only log q occurs in the final bound. -/

namespace TwoPointCorrelations

open Complex Filter
open scoped Classical Topology

theorem MRTWeakHurwitzGrowthInput.logderiv (h : MRTWeakHurwitzGrowthInput) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ (q : ℕ) [NeZero q],
      ∀ (χ : DirichletCharacter ℂ q) (t σ : ℝ), T ≤ |t| →
      1 < σ → σ ≤ 1 + mrtVKRadius (2 * t) / 16 →
        ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
            C * (mrtVKWeight q (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) := by
  obtain ⟨D, T, r₁, hD, hT, hr₁, _, hg⟩ := h.local_disks
  obtain ⟨K, r₂, hK, hr₂, hb⟩ := mrt_moving_local_logderiv
  have hrzero : Tendsto (fun x : ℝ => x ^ (-(2 / 3 : ℝ)) / 16) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 / 3 by norm_num)).div_const 16
  have hrsmall := hrzero.eventually (gt_mem_nhds (lt_min hr₁ hr₂))
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp hrsmall
  let T₀ := max T (max 7 (Real.exp (max H₀ 1)))
  have hT₀ : 0 < T₀ := hT.trans_le (le_max_left _ _)
  refine ⟨16 * K * D ^ 2, T₀, by positivity, hT₀, ?_⟩
  intro q _ χ t σ ht hσ hσr
  have htT : T ≤ |t| := (le_max_left _ _).trans ht
  have ht7 : 7 ≤ |t| := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htE : Real.exp (max H₀ 1) ≤ |t| :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hHmax : max H₀ 1 ≤ mrtVKLog (2 * t) := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < |2 * t| + 3)).mpr
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hH : 1 ≤ mrtVKLog (2 * t) := (le_max_right _ _).trans hHmax
  have hsmall := hH₀ _ ((le_max_left _ _).trans hHmax)
  have hr1 : mrtVKRadius (2 * t) / 16 ≤ r₁ := (le_of_lt hsmall).trans (min_le_left _ _)
  have hr2 : mrtVKRadius (2 * t) / 16 ≤ r₂ := (le_of_lt hsmall).trans (min_le_right _ _)
  let r := mrtVKRadius (2 * t) / 16
  have hH0 : 0 < mrtVKLog (2 * t) := mrt_VKLog_pos (2 * t)
  have hr : 0 < r := div_pos (Real.rpow_pos_of_pos hH0 _) (by norm_num)
  have hrle : r ≤ 1 / 16 := by
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 16)
    exact Real.rpow_le_one_of_one_le_of_nonpos hH (by norm_num)
  have hheight : 6 * r < |t| := by linarith
  have hw : 1 ≤ mrtVKWeight q (2 * t) := mrt_VKWeight_ge_one hH
  have hbudget : 1 ≤ D * mrtVKWeight q (2 * t) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hw)]
  have hgrowth := hg t htT hH hr1 q χ
  have hh := hb q χ r t (D * mrtVKWeight q (2 * t)) σ hr hr2 hheight hbudget
    hgrowth hσ hσr
  have hrinv : r⁻¹ = 16 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) := by
    dsimp [r]
    rw [inv_div, div_eq_mul_inv, mrtVKRadius, Real.rpow_neg hH0.le, inv_inv]
  calc
    _ ≤ K * (D * mrtVKWeight q (2 * t)) ^ 2 / r := hh
    _ = _ := by rw [div_eq_mul_inv, hrinv]; ring

end TwoPointCorrelations

end OAI
