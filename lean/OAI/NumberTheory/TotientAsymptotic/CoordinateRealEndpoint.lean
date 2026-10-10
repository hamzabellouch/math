import OAI.NumberTheory.TotientAsymptotic.EffectiveCoordinateCount

namespace OAI

/-! Rounding the endpoint of the coordinate count loses only an absolute factor. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_floor_bounds {x : ℝ} (hx : 4 ≤ x) :
    2 ≤ ⌊x⌋₊ ∧ x/2 ≤ (⌊x⌋₊:ℝ) ∧ (⌊x⌋₊:ℝ) ≤ x ∧
    Real.log x/2 ≤ Real.log (⌊x⌋₊:ℝ) ∧ B x-1 ≤ B (⌊x⌋₊:ℝ) ∧ B (⌊x⌋₊:ℝ) ≤ B x := by
  have hf := log_floor_lower hx
  have hfloor := Nat.floor_le (show 0 ≤ x by linarith)
  have hbelow := Nat.sub_one_lt_floor x
  have hlog : 0 < Real.log (⌊x⌋₊:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlow := Real.log_le_log (show 0 < Real.log x/2 by positivity) hf.2
  rw [Real.log_div hlogx.ne' (by norm_num : (2:ℝ)≠0)] at hlow
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hu : B (⌊x⌋₊:ℝ) ≤ B x :=
    Real.log_le_log hlog (Real.log_le_log (by exact_mod_cast (show 0 < ⌊x⌋₊ by omega)) hfloor)
  refine ⟨hf.1,by linarith,hfloor,hf.2,?_,hu⟩
  change Real.log (Real.log x)-1 ≤ Real.log (Real.log (⌊x⌋₊:ℝ))
  linarith

lemma coordinate_floor_normalization {x δ : ℝ} (hx : 4 ≤ x) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ)*Real.exp (-δ*B (⌊x⌋₊:ℝ)) ≤
      2*Real.exp 1*(x/Real.log x*Real.exp (-δ*B x)) := by
  have hf := coordinate_floor_bounds hx
  have hlog : 0 < Real.log (⌊x⌋₊:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hnormal : (⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ) ≤ 2*(x/Real.log x) := by
    apply (div_le_iff₀ hlog).mpr
    apply (le_trans hf.2.2.1)
    have hh := mul_le_mul_of_nonneg_left hf.2.2.2.1 (show 0 ≤ 2*x/Real.log x by positivity)
    have he : (2*x/Real.log x)*(Real.log x/2)=x := by field_simp
    rw [he] at hh
    convert hh using 1
    ring
  have hexp : Real.exp (-δ*B (⌊x⌋₊:ℝ)) ≤ Real.exp 1*Real.exp (-δ*B x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hf.2.2.2.2.1 hδ,hδ1]
  have hh := mul_le_mul hnormal hexp (Real.exp_pos _).le (by positivity : 0 ≤ 2*(x/Real.log x))
  convert hh using 1
  ring

end TotientAsymptotic

end

end OAI
