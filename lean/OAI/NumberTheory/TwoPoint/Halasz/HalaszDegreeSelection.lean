import OAI.NumberTheory.TwoPoint.Halasz.HalaszBoundedDegrees
import OAI.NumberTheory.TwoPoint.Halasz.HalaszLargeDegrees
import OAI.NumberTheory.TwoPoint.Halasz.HalaszSelectedDoubleMoment

namespace OAI

/-! Quantitative degree choices as a function of log|t|/log N. -/
namespace TwoPointCorrelations

lemma halasz_large_degree_selection {lam : ℝ} (hlam : 48≤lam) :
    8≤⌈lam/6⌉₊ ∧ 6*(⌈lam/6⌉₊:ℝ)-6≤lam ∧ lam≤6*(⌈lam/6⌉₊:ℝ) ∧
      (12*⌈lam/6⌉₊:ℝ)≤2*lam+12 := by
  have hlo := Nat.le_ceil (lam/6)
  have hhi := Nat.ceil_lt_add_one (by linarith : 0≤lam/6)
  refine ⟨?_,by linarith,by linarith,?_⟩
  · exact_mod_cast (show (8:ℝ)≤⌈lam/6⌉₊ by linarith)
  · linarith

lemma halasz_large_root_saving {m : ℕ} (hm : 8≤m) {lam : ℝ}
    (hlo : 6*(m:ℝ)-6≤lam) :
    1/((10^8:ℝ)*lam^2)≤
      (m:ℝ)^2/(4*((2*halaszSelectedMoment (12*m)*halaszSelectedMoment (12*m):ℕ):ℝ)) := by
  have hmR : (8:ℝ)≤m := by exact_mod_cast hm
  have hm0 : 0<(m:ℝ) := by linarith
  have hlam : 5*(m:ℝ)≤lam := by linarith
  have hlam0 : 0<lam := by linarith
  have hr : (halaszSelectedMoment (12*m):ℝ)≤1584*(m:ℝ)^2 := by
    simp only [halaszSelectedMoment,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    nlinarith
  have hr0 : 0<(halaszSelectedMoment (12*m):ℝ) := by
    exact_mod_cast (show 0<halaszSelectedMoment (12*m) from
      lt_of_lt_of_le Nat.zero_lt_one (halasz_selected_moment_pos (by omega)))
  have hp : 0<((2*halaszSelectedMoment (12*m)*halaszSelectedMoment (12*m):ℕ):ℝ) := by
    push_cast
    positivity
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<10^8*lam^2) (by positivity :
    (0:ℝ)<4*((2*halaszSelectedMoment (12*m)*halaszSelectedMoment (12*m):ℕ):ℝ))).mpr
  have hr2 : (halaszSelectedMoment (12*m):ℝ)^2≤1584^2*(m:ℝ)^4 := by
    calc
      _ ≤ (1584*(m:ℝ)^2)^2 := pow_le_pow_left₀ hr0.le hr 2
      _ = _ := by ring
  have hlam2 : 25*(m:ℝ)^2≤lam^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlam2 (sq_nonneg (m:ℝ))
  push_cast
  nlinarith

end TwoPointCorrelations

end OAI
