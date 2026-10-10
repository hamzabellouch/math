import OAI.NumberTheory.TotientAsymptotic.BootstrapCutoffs

namespace OAI

/-! Absorb the explicit two-coordinate grid and normality errors. -/
noncomputable section
namespace TotientAsymptotic

lemma bootstrap_grid_error {b D u : ℝ} {K : ℕ} (hb : 1 ≤ b)
    (_hu0 : 0 ≤ u) (hu : u ≤ b/100000000) (hK : (K:ℝ) ≤ b)
    (hKlow : b-Real.log (20*b)-2 ≤ K)
    (hbudget : 10000*(Real.log (20*b)+|D|+Real.log (b+1)+10) ≤ b) :
    (3/2:ℝ)*(b+5-K)+4*u+5*D+8*Real.sqrt (u*K)+2*Real.log (K+1:ℕ) ≤ b/200 := by
  have hb0 : 0 ≤ b := by linarith
  have hlog0 : 0 ≤ Real.log (20*b) := Real.log_nonneg (by linarith)
  have hlogb : 0 ≤ Real.log (b+1) := Real.log_nonneg (by linarith)
  have hlogK : Real.log (K+1:ℕ) ≤ Real.log (b+1) := by
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have hmul : u*(K:ℝ) ≤ (b/100000000)*b :=
    mul_le_mul hu hK (Nat.cast_nonneg K) (by positivity)
  have hsqrt : Real.sqrt (u*K) ≤ b/10000 := by
    apply (Real.sqrt_le_iff).mpr ⟨by positivity,?_⟩
    nlinarith only [hmul]
  have hD : D ≤ |D| := le_abs_self D
  nlinarith only [hKlow,hu,hsqrt,hlogK,hbudget,hD,hlog0,hlogb,hb]

lemma bootstrap_grid_exponential {b D u : ℝ} {K : ℕ} (hb : 1 ≤ b)
    (hu0 : 0 ≤ u) (hu : u ≤ b/100000000) (hK : (K:ℝ) ≤ b)
    (hKlow : b-Real.log (20*b)-2 ≤ K)
    (hbudget : 10000*(Real.log (20*b)+|D|+Real.log (b+1)+10) ≤ b) :
    ((K+1:ℕ):ℝ)^2*Real.exp (-(101/100:ℝ)*b+(3/2:ℝ)*(b+5-K)+4*u+5*D+
      8*Real.sqrt (u*K)) ≤ Real.exp (-(201/200:ℝ)*b) := by
  have he := bootstrap_grid_error hb hu0 hu hK hKlow hbudget
  have hpos : (0:ℝ) < (K+1:ℕ) := by positivity
  have hpow : ((K+1:ℕ):ℝ)^2 = Real.exp (Real.log (K+1:ℕ)+Real.log (K+1:ℕ)) := by
    rw [Real.exp_add,Real.exp_log hpos]
    ring
  rw [hpow,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end TotientAsymptotic

end

end OAI
