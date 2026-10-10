import OAI.NumberTheory.TotientAsymptotic.CoordinateCutoffDecay

namespace OAI

/-! Numerical decay rate used for the exceptional-value estimate. -/
noncomputable section
namespace TotientAsymptotic

def coordinateDecay (ω : ℝ) (k : ℕ) : ℝ :=
  ω^2/(12000000*((k:ℝ)+2)^6)

lemma coordinate_decay_bounds {ω : ℝ} {k : ℕ} (hω : 0 ≤ ω) (hω1 : ω ≤ 1) :
    0 ≤ coordinateDecay ω k ∧ coordinateDecay ω k ≤ 1/4 ∧
      coordinateDecay ω k ≤ ω/2 := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hp : 1 ≤ ((k:ℝ)+2)^6 := one_le_pow₀ (by linarith)
  have hd : 0 < 12000000*((k:ℝ)+2)^6 := by positivity
  have hsq : ω^2 ≤ ω := by nlinarith
  have hsq1 : ω^2 ≤ 1 := by nlinarith
  refine ⟨by unfold coordinateDecay; positivity,?_,?_⟩
  · apply (div_le_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left hp hω
    nlinarith

lemma coordinate_decay_pos {ω : ℝ} (hω : 0 < ω) (k : ℕ) :
    0 < coordinateDecay ω k := by unfold coordinateDecay; positivity

lemma coordinate_decay_identity (b ω : ℝ) (k : ℕ) :
    -ω^2*b/(6000000*((k:ℝ)+2)^6) = -2*coordinateDecay ω k*b := by
  unfold coordinateDecay
  field_simp
  ring

lemma coordinate_bootstrap_absorption {b δ : ℝ} (hb : 0 ≤ b)
    (hbudget : 9*(Real.log (b+4))^2+6*Real.log (b+4) ≤ δ*b) :
    (b+4)^6*Real.exp (9*(Real.log (b+4))^2)*Real.exp (-2*δ*b) ≤
      Real.exp (-δ*b) := by
  have hp : 0 < b+4 := by linarith
  have hid : (b+4)^6 = Real.exp (6*Real.log (b+4)) := by
    simpa only [Nat.cast_ofNat,Real.exp_log hp] using (Real.exp_nat_mul (Real.log (b+4)) 6).symm
  rw [hid,← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

lemma log_normalized_exponential {x : ℝ} (hx : 1 < x) (t : ℝ) :
    x/Real.log x*Real.exp t = x*Real.exp (t-B x) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [Real.exp_sub,B,Real.exp_log hl]
  ring

end TotientAsymptotic

end

end OAI
