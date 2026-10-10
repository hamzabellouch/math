import OAI.Analysis.LipschitzHilbert.Estimates.ActualErrorSource
import Mathlib.Analysis.Normed.Module.Basic

namespace OAI

/-! The angular multiplier error is bounded by the actual annulus-plus-
small-angle-ratio source from the manuscript. -/

noncomputable section

namespace LipschitzHilbert

def multiplierError (b : ℝ → ℂ) (t d u : ℝ) : ℂ :=
  b u - (if |u-t| ≤ d then b t else 0)

theorem multiplierError_bound (b : ℝ → ℂ) (t d c R M L u : ℝ)
    (hd : 0 < d) (_hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hb : ∀ s, ‖b s‖ ≤ M)
    (hnear : |u-t| ≤ c*d → ‖b u-b t‖ ≤ L * (|u-t|/d))
    (hfar : R*d < |u-t| → b u = 0) :
    ‖multiplierError b t d u‖ ≤ (2*M+L) * errorSourceProfile c R d |u-t| := by
  have hA : 0 ≤ 2*M+L := by positivity
  have hprofile := errorSourceProfile_nonneg c R d |u-t| hd (abs_nonneg _)
  by_cases hn : |u-t| ≤ c*d
  · have hsel : |u-t| ≤ d := hn.trans (by nlinarith)
    have hratio : 0 ≤ |u-t|/d := div_nonneg (abs_nonneg _) hd.le
    have hp : |u-t|/d ≤ errorSourceProfile c R d |u-t| := by
      unfold errorSourceProfile
      rw [ite_eq_left hn]
      split_ifs <;> linarith
    calc
      _ = ‖b u-b t‖ := by rw [multiplierError, ite_eq_left hsel]
      _ ≤ L * (|u-t|/d) := hnear hn
      _ ≤ (2*M+L) * (|u-t|/d) := mul_le_mul_of_nonneg_right (by linarith) hratio
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hA
  · by_cases hf : |u-t| ≤ R*d
    · have hp : errorSourceProfile c R d |u-t| = 1 := by
        unfold errorSourceProfile
        rw [ite_eq_left ⟨(lt_of_not_ge hn).le,hf⟩, ite_eq_right hn, add_zero]
      rw [hp,mul_one]
      unfold multiplierError
      split_ifs
      · exact (norm_sub_le _ _).trans (by linarith [hb u,hb t])
      · simpa only [sub_zero] using (hb u).trans (by linarith)
    · have hfar' : R*d < |u-t| := lt_of_not_ge hf
      have hsel : ¬ |u-t| ≤ d := by nlinarith
      rw [multiplierError, hfar hfar', ite_eq_right hsel, sub_self, norm_zero]
      exact mul_nonneg hA hprofile

end LipschitzHilbert

end

end OAI
