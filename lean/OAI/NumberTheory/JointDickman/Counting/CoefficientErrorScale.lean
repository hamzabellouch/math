import OAI.NumberTheory.JointDickman.Counting.MaskedCoefficientErrors
import OAI.NumberTheory.JointDickman.Amplification.ConditionedRootErrorLimit

namespace OAI

/-! # Coefficient-prime exclusions survive the graph's polynomial weight cap -/

namespace JointDickman
open Filter
open scoped Topology

noncomputable def coefficientRootError (B : ℕ) : ℝ :=
  72*(B : ℝ)^17/(auxiliaryCutoff B : ℝ)

theorem coefficient_error_polynomial {B N : ℕ} (hB : 2 ≤ B) (hN : N ≤ B^6)
    {a b : ℝ}
    (ha : a ≤ 12*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B))
    (hb : b ≤ 24*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)) :
    (B : ℝ)^10*(a+b) ≤ coefficientRootError B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (show 0 < auxiliaryCutoff B from pow_pos (by omega) 1000)
  have hNr : (N : ℝ) ≤ (B : ℝ)^6 := by exact_mod_cast hN
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by have h := Real.log_two_gt_d9; linarith
  have hr : 1/(Real.log 2*auxiliaryCutoff B) ≤ 2/(auxiliaryCutoff B : ℝ) := by
    have hm : (auxiliaryCutoff B : ℝ)/2 ≤ Real.log 2*auxiliaryCutoff B := by nlinarith
    exact (one_div_le_one_div_of_le (by positivity) hm).trans_eq (by ring)
  calc
    _ ≤ (B : ℝ)^10*(12*(N : ℝ)*B/(Real.log 2*auxiliaryCutoff B)+
        24*(N : ℝ)*B/(Real.log 2*auxiliaryCutoff B)) :=
      mul_le_mul_of_nonneg_left (add_le_add ha hb) (by positivity)
    _ = 36*(B : ℝ)^10*(N : ℝ)*B*(1/(Real.log 2*auxiliaryCutoff B)) := by ring
    _ ≤ 36*(B : ℝ)^10*((B : ℝ)^6)*B*(2/(auxiliaryCutoff B : ℝ)) := by gcongr
    _ = coefficientRootError B := by unfold coefficientRootError; ring

theorem coefficientRootError_tendsto :
    Tendsto coefficientRootError atTop (𝓝 0) := by
  have h := (polynomial_div_primeCutoff_tendsto_zero (k := 17) (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun B : ℕ => (B : ℝ)^17/(auxiliaryCutoff B : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,auxiliaryCutoff,Nat.cast_pow] using h
  have ht := hh.const_mul 72
  simp only [mul_zero] at ht
  convert ht using 1
  funext B
  unfold coefficientRootError
  ring

end JointDickman

end OAI
