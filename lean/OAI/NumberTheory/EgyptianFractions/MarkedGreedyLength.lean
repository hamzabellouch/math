import OAI.NumberTheory.EgyptianFractions.MarkedGreedy
import OAI.NumberTheory.EgyptianFractions.RepeatedSquaring

namespace OAI
noncomputable section
namespace Problem337

/-- Each ordinary step squares the remainder; we count only these steps. -/
theorem MarkedGreedySteps.remainder_le_pow_count {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) (hq : 0 < q)
    (a : ℚ) (ha : 0 ≤ a) (hstart : (R : ℚ) / q ≤ a) :
    (Rf : ℚ) / qf ≤ a ^ (2 ^ (L.filter (fun n => n ≠ m + 1)).length) := by
  induction h generalizing a with
  | nil R q => simpa using hstart
  | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail ih =>
    have hn0 : 0 < n := by omega
    have hqnext : 0 < n * q := Nat.mul_pos hn0 hq
    have hR : 0 < R := by nlinarith
    have hR_Q : (0 : ℚ) ≤ (R : ℚ) / q := by positivity
    have htail_nonneg : (0 : ℚ) ≤ (c : ℚ) / (n * q : ℕ) := by positivity
    by_cases hne : n ≠ m + 1
    · have hsq : (c : ℚ) / (n * q : ℕ) ≤ a ^ 2 :=
        (marked_greedy_square R q n c hR hq hn0 heq (hord hne)).le.trans
          (pow_le_pow_left₀ hR_Q hstart 2)
      have hres := ih hqnext (a ^ 2) (by positivity) hsq
      have hlen : ((n :: L).filter (fun b => b ≠ m + 1)).length =
          (L.filter (fun b => b ≠ m + 1)).length + 1 := by simp [hne]
      rw [hlen]
      calc
        (Rf : ℚ) / qf ≤ (a ^ 2) ^ (2 ^ (L.filter (fun b => b ≠ m + 1)).length) := hres
        _ = a ^ (2 ^ ((L.filter (fun b => b ≠ m + 1)).length + 1)) := by
          rw [← pow_mul, pow_succ]
          congr 1
          exact Nat.mul_comm _ _
    · have heqQ : (n : ℚ) * R = q + c := by exact_mod_cast heq
      have hnQ : (0 : ℚ) < n := by exact_mod_cast hn0
      have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
      have hdec : (c : ℚ) / (n * q : ℕ) ≤ (R : ℚ) / q := by
        push_cast
        apply (div_le_div_iff₀ (mul_pos hnQ hqQ) hqQ).2
        nlinarith
      have hres := ih hqnext a ha (hdec.trans hstart)
      simpa [hne] using hres

/-- In a duplicate-free list, discarding one specified value loses at most one term. -/
theorem length_le_filter_ne_add_one (L : List ℕ) (c : ℕ) (hL : L.Nodup) :
    L.length ≤ (L.filter (fun n => n ≠ c)).length + 1 := by
  induction L with
  | nil => simp
  | cons n L ih =>
    obtain ⟨hn, htail⟩ := List.nodup_cons.mp hL
    by_cases hnc : n = c
    · subst n
      have hfilter : L.filter (fun n => n ≠ c) = L := by
        apply List.filter_eq_self.mpr
        intro a ha
        simp only [decide_eq_true_eq]
        intro hac
        subst a
        exact hn ha
      rw [List.filter_cons_of_neg (by simp), hfilter]
      simp
    · have hi := ih htail
      simpa [hnc] using Nat.succ_le_succ hi

/-- A duplicate-free marked trace has at most one non-squaring step. -/
theorem MarkedGreedySteps.remainder_le_half_pow_length {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) (hq : 0 < q)
    (hL : L.Nodup) (hstart : (R : ℚ) / q ≤ (1 / 2 : ℚ)) :
    (Rf : ℚ) / qf ≤ (1 / 2 : ℚ) ^ (2 ^ (L.length - 1)) := by
  have hcount := h.remainder_le_pow_count hq (1 / 2) (by norm_num) hstart
  have hlen := length_le_filter_ne_add_one L (m + 1) hL
  apply hcount.trans
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  apply Nat.pow_le_pow_right (by omega : 1 ≤ 2)
  omega

/-- A marked greedy trace with a last active denominator below T has the
sharp double-logarithmic prefix length bound. -/
theorem MarkedGreedySteps.length_lt_loglog {m R q T : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m (m - 1) m L R q) (hm : 4 ≤ m)
    (hL : L.Nodup) (hT : 2 ≤ T)
    (hactive : L ≠ [] → m * L.dropLast.prod < T) :
    (L.length : ℝ) < 3 + Real.log (Real.log (T : ℝ) / Real.log 2) / Real.log 2 := by
  by_cases hlen : 3 ≤ L.length
  · have hne : L ≠ [] := by intro he; simp [he] at hlen
    obtain ⟨Ri, qi, hpre, hRi, hqi, hqeq⟩ := h.penultimate hne
    have hqiT : qi < T := by rw [hqeq]; exact hactive hne
    cases hP : L.dropLast with
    | nil =>
      have hlenP := congrArg List.length hP
      simp only [List.length_dropLast, List.length_nil] at hlenP
      omega
    | cons n S =>
      have hpre' : MarkedGreedySteps m (m - 1) m (n :: S) Ri qi := by
        simpa only [hP] using hpre
      obtain ⟨hn, htail⟩ := hpre'.first hm
      have hSnodup : S.Nodup := by
        have hPnodup := List.Nodup.sublist (List.dropLast_sublist L) hL
        rw [hP] at hPnodup
        exact (List.nodup_cons.mp hPnodup).2
      have hstart : ((m - 2 : ℕ) : ℚ) / (2 * m : ℕ) ≤ (1 / 2 : ℚ) := by
        have hden : (0 : ℚ) < (2 * m : ℕ) := by positivity
        apply (div_le_iff₀ hden).2
        have hsub : ((m - 2 : ℕ) : ℚ) ≤ (m : ℚ) := by
          exact_mod_cast Nat.sub_le m 2
        push_cast
        nlinarith
      have hrem := htail.remainder_le_half_pow_length (by omega) hSnodup hstart
      have hlenP := congrArg List.length hP
      simp only [List.length_dropLast, List.length_cons] at hlenP
      have hexp : S.length - 1 = L.length - 3 := by omega
      rw [hexp] at hrem
      have hden := nat_denominator_bound_of_small_remainder Ri qi
        (2 ^ (L.length - 3)) hRi hqi hrem
      apply marked_prefix_length_of_double_power L.length (T : ℝ) hlen
      exact_mod_cast hden.trans_lt hqiT
  · have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlogT : Real.log (2 : ℝ) ≤ Real.log (T : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hT)
    have hratio : 1 ≤ Real.log (T : ℝ) / Real.log 2 := by
      apply (le_div_iff₀ hlog2).2
      simpa using hlogT
    have hnonneg : 0 ≤ Real.log (Real.log (T : ℝ) / Real.log 2) / Real.log 2 :=
      div_nonneg (Real.log_nonneg hratio) hlog2.le
    have hlenR : (L.length : ℝ) < 3 := by exact_mod_cast (show L.length < 3 by omega)
    linarith

/-- The marked greedy prefix, now including its quantitative term budget. -/
theorem exists_marked_greedy_prefix_short (m T : ℕ)
    (hm : 4 ≤ m) (hT : 2 * m ^ 2 ≤ T) :
    ∃ L : List ℕ, ∃ R q : ℕ,
      MarkedGreedySteps m (m - 1) m L R q ∧
      L.Pairwise (· < ·) ∧ (∀ n ∈ L, 2 ≤ n ∧ n ≠ m) ∧
      q = m * L.prod ∧ 0 < q ∧ R < 2 * m ∧
      (1 : ℚ) = 1 / (m : ℚ) + (L.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum + (R : ℚ) / q ∧
      q < T ^ 2 ∧ (R = 0 ∨ T ≤ q) ∧
      m * R < q ∧ (∀ n ∈ L, n * R < q) ∧
      (L.length : ℝ) < 3 + Real.log (Real.log (T : ℝ) / Real.log 2) / Real.log 2 := by
  obtain ⟨L, R, q, htrace, hpair, hden, hqeq, hqpos, hRsmall, hsum,
    hqbound, hstop, hmarker, hfinal, hactive⟩ := exists_marked_greedy_prefix_bounded m T hm hT
  have hnodup : L.Nodup := hpair.imp (fun h => ne_of_lt h)
  have hT2 : 2 ≤ T := by nlinarith
  exact ⟨L, R, q, htrace, hpair, hden, hqeq, hqpos, hRsmall, hsum,
    hqbound, hstop, hmarker, hfinal, htrace.length_lt_loglog hm hnodup hT2 hactive⟩

end Problem337

end

end OAI
