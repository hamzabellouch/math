import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Divisors at every multiplicative scale, in the form used by grouping. -/
def HasMarkedDivisorDensity (m q : ℕ) : Prop :=
  ∀ w : ℝ, 1 ≤ w → w ≤ (q : ℝ) →
    ∃ d : ℕ, 0 < d ∧ d ∣ q ∧ w / (m : ℝ) ≤ (d : ℝ) ∧ (d : ℝ) ≤ w

/-- One group strictly shrinks the remaining numerator by a factor `m²`. -/
theorem marked_grouping_step (m q X : ℕ) (hm : 2 ≤ m)
    (hX : m ^ 4 < X) (hXq : X ≤ q)
    (hdensity : HasMarkedDivisorDensity m q) :
    ∃ d s R : ℕ, 0 < d ∧ d ∣ q ∧ 1 ≤ s ∧ s ≤ m ^ 4 ∧
      X = d * s + R ∧ R * m ^ 2 < X := by
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hm2R : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos hmR 2
  have hm2 : m ^ 2 ≤ m ^ 4 := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hw1 : (1 : ℝ) ≤ (X : ℝ) / (m : ℝ) ^ 2 := by
    apply (le_div_iff₀ hm2R).2
    norm_num
    exact_mod_cast (hm2.trans hX.le)
  have hwq : (X : ℝ) / (m : ℝ) ^ 2 ≤ (q : ℝ) := by
    apply (div_le_iff₀ hm2R).2
    have hm21 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      exact_mod_cast (show 1 ≤ m ^ 2 by have : 0 < m ^ 2 := pow_pos hm0 2; omega)
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hXqR : (X : ℝ) ≤ q := by exact_mod_cast hXq
    nlinarith
  obtain ⟨d, hd0, hdq, hdl, hdu⟩ := hdensity _ hw1 hwq
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hupper : d * m ^ 2 ≤ X := by
    have h := (le_div_iff₀ hm2R).1 hdu
    exact_mod_cast h
  have hlower : X ≤ d * m ^ 3 := by
    have h := (div_le_iff₀ hmR).1 hdl
    have h' := (div_le_iff₀ hm2R).1 h
    have heq : (d : ℝ) * (m : ℝ) * (m : ℝ) ^ 2 = (d : ℝ) * (m : ℝ) ^ 3 := by ring
    rw [heq] at h'
    exact_mod_cast h'
  refine ⟨d, X / d, X % d, hd0, hdq, ?_, ?_, ?_, ?_⟩
  · have hdm : d ≤ d * m ^ 2 := Nat.le_mul_of_pos_right d (by positivity)
    exact Nat.le_div_iff_mul_le hd0 |>.2 (by simpa using hdm.trans hupper)
  · have hdiv : X / d ≤ m ^ 3 := (Nat.div_le_iff_le_mul_add_pred hd0).2 (by omega)
    exact hdiv.trans (Nat.pow_le_pow_right (by omega) (by omega))
  · exact (Nat.div_add_mod X d).symm
  · have hmod : X % d < d := Nat.mod_lt X hd0
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hmod (by positivity)) hupper

/-- Discrete grouping bound: a numerator below `(m²)^t` needs at most `t` groups. -/
theorem marked_grouping_lt_pow (m q : ℕ) (hm : 2 ≤ m)
    (hdensity : HasMarkedDivisorDensity m q) (t X : ℕ)
    (hXq : X ≤ q) (hpow : X < (m ^ 2) ^ t) :
    ∃ groups : List (ℕ × ℕ), groups.length ≤ t ∧
      (∀ g ∈ groups, 0 < g.1 ∧ g.1 ∣ q ∧ 1 ≤ g.2 ∧ g.2 ≤ m ^ 4) ∧
      (groups.map (fun g => g.1 * g.2)).sum = X := by
  induction t generalizing X with
  | zero =>
      have hX : X = 0 := by simpa using hpow
      subst X
      exact ⟨[], by simp⟩
  | succ t ih =>
      by_cases hzero : X = 0
      · subst X
        exact ⟨[], by simp⟩
      by_cases hsmall : X ≤ m ^ 4
      · refine ⟨[(1, X)], by simp, ?_, by simp⟩
        intro g hg
        simp only [List.mem_singleton] at hg
        subst g
        exact ⟨by omega, one_dvd q, by omega, hsmall⟩
      obtain ⟨d, s, R, hd, hdq, hs, hsm, heq, hshrink⟩ :=
        marked_grouping_step m q X hm (by omega) hXq hdensity
      have hm2 : 0 < m ^ 2 := pow_pos (by omega) 2
      have hRpow : R < (m ^ 2) ^ t := by
        rw [pow_succ] at hpow
        exact Nat.lt_of_mul_lt_mul_right (hshrink.trans hpow)
      have hRX : R < X := by
        have hle : R ≤ R * m ^ 2 := Nat.le_mul_of_pos_right R hm2
        exact hle.trans_lt hshrink
      obtain ⟨groups, hlen, hgroups, hsum⟩ := ih R (by omega) hRpow
      refine ⟨(d, s) :: groups, by simpa using Nat.succ_le_succ hlen, ?_, ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨hd, hdq, hs, hsm⟩
        · exact hgroups g hg
      · simpa [hsum] using heq.symm

/-- The elementary grouping construction with its real logarithmic length bound. -/
theorem marked_grouping (m q X : ℕ) (hm : 2 ≤ m)
    (hdensity : HasMarkedDivisorDensity m q) (hXq : X ≤ q) :
    ∃ groups : List (ℕ × ℕ),
      (groups.length : ℝ) ≤ Real.log (X : ℝ) / (2 * Real.log (m : ℝ)) + 1 ∧
      (∀ g ∈ groups, 0 < g.1 ∧ g.1 ∣ q ∧ 1 ≤ g.2 ∧ g.2 ≤ m ^ 4) ∧
      (groups.map (fun g => g.1 * g.2)).sum = X := by
  have hm2 : 1 < m ^ 2 := by nlinarith
  obtain ⟨groups, hlen, hgroups, hsum⟩ := marked_grouping_lt_pow m q hm hdensity
    (Nat.log (m ^ 2) X + 1) X hXq (Nat.lt_pow_succ_log_self hm2 X)
  refine ⟨groups, ?_, hgroups, hsum⟩
  have hlenR : (groups.length : ℝ) ≤ (Nat.log (m ^ 2) X : ℝ) + 1 := by
    exact_mod_cast hlen
  have hlog := Real.natLog_le_logb X (m ^ 2)
  simp only [Real.logb, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at hlog
  linarith

end Problem337

end

end OAI
