import OAI.Probability.SATComputability.RelaxedPressure

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset
open scoped BigOperators

noncomputable def relaxedMinimumViolations {n m : ℕ}
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) : ℕ :=
  Nat.find (show ∃ v : ℕ, ∃ s : Fin n → Bool,
      relaxedViolations s indices signs = v from
    ⟨relaxedViolations (fun _ => false) indices signs, (fun _ => false), rfl⟩)

theorem relaxedMinimum_attained {n m : ℕ}
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    ∃ s, relaxedViolations s indices signs = relaxedMinimumViolations indices signs := by
  unfold relaxedMinimumViolations
  exact Nat.find_spec (p := fun v => ∃ s, relaxedViolations s indices signs = v) _

theorem relaxedMinimum_le {n m : ℕ}
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) (s : Fin n → Bool) :
    relaxedMinimumViolations indices signs ≤ relaxedViolations s indices signs :=
  Nat.find_min' _ ⟨s, rfl⟩

theorem relaxedMinimum_gt_of_deletion_unsat {n m r : ℕ}
    {indices : Fin m → Fin 3 → Fin n} {signs : Fin m → Fin 3 → Bool}
    (h : ¬deletionSatisfiable r indices signs) :
    r < relaxedMinimumViolations indices signs := by
  obtain ⟨s, hs⟩ := relaxedMinimum_attained indices signs
  rw [← hs]
  exact violations_gt_of_deletion_unsat h s

theorem relaxedLogPartition_lower {n m : ℕ} (β : ℝ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    -β * relaxedMinimumViolations indices signs ≤ relaxedLogPartition β indices signs := by
  obtain ⟨s, hs⟩ := relaxedMinimum_attained indices signs
  have he : Real.exp (-β * relaxedMinimumViolations indices signs) ≤
      relaxedPartition β indices signs := by
    rw [← hs]
    exact Finset.single_le_sum (fun a _ =>
      (Real.exp_pos (-β * relaxedViolations a indices signs)).le) (Finset.mem_univ s)
  have := Real.log_le_log (Real.exp_pos _) he
  simpa only [Real.log_exp, relaxedLogPartition] using this

theorem relaxedLogPartition_upper {n m : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    relaxedLogPartition β indices signs ≤
      n * Real.log 2 - β * relaxedMinimumViolations indices signs := by
  have hb : relaxedPartition β indices signs ≤ (2 : ℝ)^n *
      Real.exp (-β * relaxedMinimumViolations indices signs) := by
    calc
      _ ≤ ∑ _s : Fin n → Bool, Real.exp (-β * relaxedMinimumViolations indices signs) := by
        apply Finset.sum_le_sum
        intro s _
        apply Real.exp_le_exp.mpr
        have h : (relaxedMinimumViolations indices signs : ℝ) ≤
            relaxedViolations s indices signs := by exact_mod_cast relaxedMinimum_le indices signs s
        nlinarith
      _ = _ := by simp
  have hz : 0 < relaxedPartition β indices signs :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have h := Real.log_le_log hz hb
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at h
  simpa only [relaxedLogPartition, sub_eq_add_neg, neg_mul] using h

theorem relaxedMinimum_time_lower {n m r : ℕ} {a τ : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hτ : 0 ≤ τ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool)
    (hsurvive : deletionSatisfiable r indices signs → a*n ≤ τ) :
    (r : ℝ) * (1 - τ/(a*n)) ≤ relaxedMinimumViolations indices signs := by
  have hden : 0 < a*(n : ℝ) := mul_pos ha (by exact_mod_cast hn)
  by_cases hs : deletionSatisfiable r indices signs
  · have htime : 1 ≤ τ/(a*n) := (le_div_iff₀ hden).mpr (by simpa using hsurvive hs)
    exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg r)
      (show (1 : ℝ) - τ/(a*n) ≤ 0 by linarith)).trans
      (Nat.cast_nonneg _)
  · have hm : (r : ℝ) ≤ relaxedMinimumViolations indices signs := by
      exact_mod_cast (relaxedMinimum_gt_of_deletion_unsat hs).le
    have ht : 0 ≤ τ/(a*n) := div_nonneg hτ hden.le
    nlinarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]

end FixedClauseThreshold.Computability

end OAI
