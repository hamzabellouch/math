import OAI.Combinatorics.GraphThreshold.Thresholds
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI

/-!
# Explicit constants in the threshold conclusion

The tree argument first gives a logarithm of an edge capacity.  These elementary
bounds turn that quantity into the two constants stated for graphs.
-/

noncomputable section

namespace LeanBlast.SecondKahnKalai

theorem logTwo_eq_logb (x : ℝ) : logTwo x = Real.logb 2 x := rfl

theorem logTwo_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ logTwo x := by
  unfold logTwo
  exact div_nonneg (Real.log_nonneg hx) (Real.log_pos (by norm_num)).le

theorem logTwo_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    logTwo x ≤ logTwo y := by
  unfold logTwo
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (Real.log_pos (by norm_num)).le

theorem edgeCount_le_sq {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    edgeCount H ≤ n ^ 2 := by
  classical
  rw [edgeCount_eq_card_edgeFinset]
  calc
    H.edgeFinset.card ≤ (Fintype.card V).choose 2 :=
      SimpleGraph.card_edgeFinset_le_card_choose_two
    _ ≤ (Fintype.card V) ^ 2 := Nat.choose_le_pow _ _
    _ ≤ n ^ 2 := Nat.pow_le_pow_left hcard 2

theorem one_add_logTwo_le_three_logTwo (n h : ℕ)
    (hn : 2 ≤ n) (hh : 1 ≤ h) (hhn : h ≤ n ^ 2) :
    1 + logTwo (h : ℝ) ≤ 3 * logTwo (n : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hhn' : (h : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hhn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hn'
  have hone : 1 ≤ logTwo (n : ℝ) := by
    unfold logTwo
    exact (le_div_iff₀ hlog2).mpr (by simpa using hlogn)
  have hlogh : Real.log (h : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    calc
      Real.log (h : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by linarith) hhn'
      _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
  have htwo : logTwo (h : ℝ) ≤ 2 * logTwo (n : ℝ) := by
    unfold logTwo
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right hlogh hlog2.le
  linarith

theorem graph_one_add_logTwo_le_three_logTwo {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hn : 2 ≤ n)
    (hcard : Fintype.card V ≤ n) (hedge : 1 ≤ edgeCount H) :
    1 + logTwo (edgeCount H : ℝ) ≤ 3 * logTwo (n : ℝ) :=
  one_add_logTwo_le_three_logTwo n (edgeCount H) hn hedge
    (edgeCount_le_sq n H hcard)

theorem graphThresholdParameter_mem_unitInterval (q : ℝ) (h : ℕ)
    (hq : 0 ≤ q) (hh : 1 ≤ h) :
    min 1 (2048 * Real.exp 50 * q * (1 + logTwo (h : ℝ))) ∈ Set.Icc 0 1 := by
  have hlog : 0 ≤ logTwo (h : ℝ) := logTwo_nonneg (by exact_mod_cast hh)
  constructor
  · exact le_min (by norm_num) (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 50).le) hq) (by linarith))
  · exact min_le_left _ _

theorem treeSamplingParameter_mem_unitInterval (q : ℝ) (m : ℕ)
    (hq : 0 ≤ q) (hm : 0 < m) :
    min 1 (16 * Real.exp 50 * (128 * q) *
      (1 + Real.logb 2 (m : ℝ))) ∈ Set.Icc 0 1 := by
  have hfactor : 16 * Real.exp 50 * (128 * q) = 2048 * Real.exp 50 * q := by ring
  rw [hfactor, ← logTwo_eq_logb]
  exact graphThresholdParameter_mem_unitInterval q m hq hm

theorem treeSamplingParameter_le_graphParameter (q : ℝ) (m h : ℕ)
    (hq : 0 ≤ q) (hm : 0 < m) (hmh : m ≤ h) :
    min 1 (16 * Real.exp 50 * (128 * q) * (1 + Real.logb 2 (m : ℝ))) ≤
      min 1 (2048 * Real.exp 50 * q * (1 + logTwo (h : ℝ))) := by
  apply min_le_min_left
  have hlog : logTwo (m : ℝ) ≤ logTwo (h : ℝ) :=
    logTwo_mono (by exact_mod_cast hm) (by exact_mod_cast hmh)
  calc
    16 * Real.exp 50 * (128 * q) * (1 + Real.logb 2 (m : ℝ)) =
        2048 * Real.exp 50 * q * (1 + logTwo (m : ℝ)) := by
      rw [logTwo_eq_logb]
      ring
    _ ≤ 2048 * Real.exp 50 * q * (1 + logTwo (h : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 50).le) hq)

theorem graphThresholdParameter_le_vertexBound {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (q : ℝ) (hn : 2 ≤ n)
    (hcard : Fintype.card V ≤ n) (hedge : 1 ≤ edgeCount H) (hq : 0 ≤ q) :
    min 1 (2048 * Real.exp 50 * q * (1 + logTwo (edgeCount H : ℝ))) ≤
      6144 * Real.exp 50 * q * logTwo (n : ℝ) := by
  calc
    min 1 (2048 * Real.exp 50 * q * (1 + logTwo (edgeCount H : ℝ))) ≤
        2048 * Real.exp 50 * q * (1 + logTwo (edgeCount H : ℝ)) := min_le_right _ _
    _ ≤ 2048 * Real.exp 50 * q * (3 * logTwo (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (graph_one_add_logTwo_le_three_logTwo n H hn hcard hedge)
        (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 50).le) hq)
    _ = 6144 * Real.exp 50 * q * logTwo (n : ℝ) := by ring

end LeanBlast.SecondKahnKalai

end

end OAI
