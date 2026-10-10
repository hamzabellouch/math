import OAI.Combinatorics.ContingencyTables.Transport.IntegerLeafTransport
import OAI.Combinatorics.ContingencyTables.Transport.IntegerTransportLevels

namespace OAI

/-! # Root auxiliary defects in the raw integer transport bound -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix

noncomputable def rootCoefficients (s t : ℝ) : Bool → ℝ :=
  fun b => if b then -(1/t) else 1/s

lemma root_potential (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    (∑ b : Bool, (if b then t else s) * rootCoefficients s t b ^ 2) = 1/s+1/t := by
  simp only [Fintype.sum_bool, rootCoefficients, Bool.false_eq_true, ↓reduceIte, neg_sq]
  field_simp [ne_of_gt hs, ne_of_gt ht]
  ring

/-- Only the off-diagonal auxiliary defects can increase the root bound;
nonnegative diagonal two-hole masses contribute with the opposite sign. -/
theorem root_future_bound (B : Matrix Bool Bool ℝ) (s t K c : ℝ)
    (hs : 0<s) (ht : 0<t) (hsymm : B true false = B false true)
    (haa : 0≤B false false) (hbb : 0≤B true true)
    (hab : B false true ≤ K*c) :
    -B.toBilin' (rootCoefficients s t) (rootCoefficients s t) ≤ 2*K*c/(s*t) := by
  have heq : B.toBilin' (rootCoefficients s t) (rootCoefficients s t) =
      B false false/s^2 - 2*B false true/(s*t) + B true true/t^2 := by
    simp only [Matrix.toBilin'_apply, Fintype.sum_bool, rootCoefficients, Bool.false_eq_true, ↓reduceIte, hsymm]
    ring
  rw [heq]
  have ha : 0 ≤ B false false/s^2 := div_nonneg haa (sq_nonneg _)
  have hb : 0 ≤ B true true/t^2 := div_nonneg hbb (sq_nonneg _)
  have hc : 2*B false true/(s*t) ≤ 2*K*c/(s*t) := by
    simpa only [mul_assoc] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hab (show (0:ℝ)≤2 by norm_num)) (mul_pos hs ht).le
  linarith

/-- The manuscript's last scalar step uses the auxiliary repair injection
only through c_t<=max(s,t). The two positive endpoint masses are retained
through every denominator. -/
theorem root_coefficient_after_repair (s t c : ℝ) (U d : ℕ)
    (hs : 0<s) (ht : 0<t) (hc : c ≤ (d:ℝ)*max s t) :
    min s t * (1/s + 1/t + 2*((U:ℝ)+1)^2*c/(s*t)) ≤
      2 + 2*(d:ℝ)*((U:ℝ)+1)^2 := by
  have hmul : min s t * max s t = s*t := min_mul_max s t
  have hmin : 0 < min s t := lt_min hs ht
  have hratio : min s t * (1/s+1/t) ≤ 2 := by
    have ha : min s t/s ≤ 1 := (div_le_one hs).mpr (min_le_left _ _)
    have hb : min s t/t ≤ 1 := (div_le_one ht).mpr (min_le_right _ _)
    calc
      _ = min s t/s + min s t/t := by ring
      _ ≤ 2 := by linarith
  have haux : min s t*c/(s*t) ≤ d := by
    apply (div_le_iff₀ (mul_pos hs ht)).mpr
    calc
      _ ≤ min s t*((d:ℝ)*max s t) := mul_le_mul_of_nonneg_left hc hmin.le
      _ = _ := by rw [mul_left_comm, hmul]
  have hm := mul_le_mul_of_nonneg_left haux
    (show 0 ≤ 2*((U:ℝ)+1)^2 by positivity)
  have halg : min s t * (1/s + 1/t + 2*((U:ℝ)+1)^2*c/(s*t)) =
      min s t * (1/s+1/t) + (2*((U:ℝ)+1)^2)*(min s t*c/(s*t)) := by ring
  rw [halg]
  nlinarith

end ContingencyTables.IntegerWeightedTransport

end OAI
