import OAI.NumberTheory.TotientAsymptotic.SmoothTotientCount
import OAI.NumberTheory.TotientAsymptotic.BootstrapSquareDecay

namespace OAI

/-! A slowly growing smoothness cutoff for the exceptional-cofactor count. -/
noncomputable section
namespace TotientAsymptotic

def movingSmoothCutoff (x : ℝ) : ℕ :=
  ⌊Real.exp (Real.log x/(500*B x))⌋₊

lemma moving_smooth_budget {x : ℝ} (hx : 1 < x) (hB : 10000 ≤ B x) :
    2 ≤ movingSmoothCutoff x ∧ 0 < Real.log (movingSmoothCutoff x) ∧
    Real.log (movingSmoothCutoff x) ≤ Real.log x ∧
    60*B x ≤ (Real.log x/2)/(4*Real.log (movingSmoothCutoff x)) ∧
    6*B x ≤ Real.log x := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hb : 0 < B x := by linarith
  have he : Real.exp (B x)=Real.log x := Real.exp_log hl
  have hquad := exp_quadratic_lower hb.le
  rw [he] at hquad
  have hmass : 2000*B x ≤ Real.log x := by nlinarith only [hquad,hB]
  have hdiv : 4 ≤ Real.log x/(500*B x) := (le_div_iff₀ (by positivity)).mpr (by linarith only [hmass])
  have hK : 2 ≤ movingSmoothCutoff x := by
    apply Nat.le_floor
    have hh := Real.add_one_le_exp (Real.log x/(500*B x))
    linarith only [hh,hdiv]
  have hK0 : (0:ℝ) < movingSmoothCutoff x := by exact_mod_cast (show 0 < movingSmoothCutoff x by omega)
  have hK1 : (1:ℝ) < movingSmoothCutoff x := by exact_mod_cast (show 1 < movingSmoothCutoff x by omega)
  have hlogK : 0 < Real.log (movingSmoothCutoff x) := Real.log_pos hK1
  have hlog : Real.log (movingSmoothCutoff x) ≤ Real.log x/(500*B x) := by
    have hh := Real.log_le_log hK0 (Nat.floor_le (Real.exp_pos _).le)
    simpa only [Real.log_exp,movingSmoothCutoff] using hh
  have hproduct : 500*B x*Real.log (movingSmoothCutoff x) ≤ Real.log x := by
    have hh := (le_div_iff₀ (show 0 < 500*B x by positivity)).mp hlog
    nlinarith only [hh]
  refine ⟨hK,hlogK,?_,?_,by linarith only [hmass,hb]⟩
  · have hscale : 1 ≤ 500*B x := by linarith only [hB]
    nlinarith only [hproduct,mul_le_mul_of_nonneg_right hscale hlogK.le]
  · apply (le_div_iff₀ (by positivity : 0 < 4*Real.log (movingSmoothCutoff x))).mpr
    nlinarith only [hproduct,mul_pos hb hlogK]

lemma moving_smooth_rankin_factor {x : ℝ} (hx : 1 < x) (hB : 10000 ≤ B x) :
    Real.exp (-(Real.log x/2)/(4*Real.log (movingSmoothCutoff x))) ≤ Real.exp (-60*B x) := by
  apply Real.exp_le_exp.mpr
  have hh := (moving_smooth_budget hx hB).2.2.2.1
  simpa only [neg_div,neg_mul] using neg_le_neg hh

end TotientAsymptotic

end

end OAI
