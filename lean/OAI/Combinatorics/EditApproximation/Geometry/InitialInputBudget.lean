import OAI.Combinatorics.EditApproximation.Geometry.LocalInitialCones
import OAI.Combinatorics.EditApproximation.Geometry.WideActions

namespace OAI

/-! The local initial cone uses a bounded number of preceding-seed
queries on every clamped seed, independently of an accuracy event. -/

namespace EditApproximation

theorem localTargetStates_length_from_scale {n : ℕ} (P b radius C : ℕ)
    (q : TargetInterval n) (hP : 0 < P) (hradius : radius ≤ C * b) :
    (localTargetStates n (seedGridSpacing b P) radius q).length ≤ (4 * C * P + 2) ^ 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hcover : b ≤ 2 * P * seedGridSpacing b P := by
    have hquot : b / P ≤ seedGridSpacing b P := le_max_right _ _
    have hdiv := Nat.lt_mul_div_succ b hP
    nlinarith only [hquot, hdiv, hg]
  have hprod : 2 * radius ≤ 4 * C * P * seedGridSpacing b P := by
    nlinarith only [hradius, Nat.mul_le_mul_left (2 * C) hcover]
  have hcount : 2 * radius / seedGridSpacing b P ≤ 4 * C * P := by
    have hdivision := Nat.div_mul_le_self (2 * radius) (seedGridSpacing b P)
    nlinarith only [hdivision, hprod, hg]
  exact (localTargetStates_length_le hg q).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right hcount 2) 2)

theorem localInitialConeCenters_length {n : ℕ} (N P Amax : ℕ) (A : ℚ)
    (U : TargetInterval n → ℕ) (q : TargetInterval n)
    (hP : 0 < P) (hA : 1 ≤ A) (hAmax : A ≤ Amax) :
    (localInitialConeCenters N P A U q).length ≤
      (dyadicScales N).length * (64 * Amax ^ 2 * P + 2) ^ 2 := by
  unfold localInitialConeCenters
  apply (list_flatMap_length_le _ _ _ ?_).trans
    (Nat.mul_le_mul_right _ (List.length_filter_le _ _))
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hAr : 0 < A := by linarith
  have hscale : (U q : ℚ) ≤ 16 * A ^ 2 * b := by
    have h := (div_le_iff₀ (by positivity : (0 : ℚ) < 16 * A ^ 2)).mp hwindow.1
    nlinarith only [h]
  have hAsq : A ^ 2 ≤ (Amax : ℚ) ^ 2 :=
    pow_le_pow_left₀ hAr.le hAmax 2
  have hradius : U q ≤ 16 * Amax ^ 2 * b := by
    have hmul := mul_le_mul_of_nonneg_right hAsq (by positivity : (0 : ℚ) ≤ 16 * b)
    have hr : (U q : ℚ) ≤ (16 * Amax ^ 2 * b : ℕ) := by
      push_cast
      nlinarith only [hscale, hmul]
    exact_mod_cast hr
  exact (List.length_filter_le _ _).trans
    (by simpa only [show 4 * (16 * Amax ^ 2) * P = 64 * Amax ^ 2 * P by ring] using
      localTargetStates_length_from_scale P b (U q) (16 * Amax ^ 2) q hP hradius)

end EditApproximation

end OAI
