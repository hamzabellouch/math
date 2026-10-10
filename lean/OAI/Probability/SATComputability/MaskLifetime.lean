import OAI.Probability.SATComputability.CandidateMasks
import OAI.Probability.SATComputability.DiscreteDelay

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators NNReal Classical

noncomputable def maskLifetime {n : ℕ} : (m : ℕ) → Finset (DeletionCandidate n) →
    (Fin m → Finset (DeletionCandidate n)) → ℝ
  | 0, _, _ => 0
  | m+1, U, xs => candidateAlive U + maskLifetime m (U ∩ xs 0) (Fin.tail xs)

theorem maskLifetime_nonneg {n m : ℕ} (U : Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) : 0 ≤ maskLifetime m U xs := by
  induction m generalizing U with
  | zero => exact (le_rfl : (0 : ℝ) ≤ 0)
  | succ m ih => exact add_nonneg (candidateAlive_nonneg U) (ih _ _)

theorem maskLifetime_le {n m : ℕ} (U : Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) : maskLifetime m U xs ≤ m := by
  induction m generalizing U with
  | zero => simp [maskLifetime]
  | succ m ih =>
    simp only [maskLifetime, Nat.cast_add, Nat.cast_one]
    linarith [candidateAlive_le_one U, ih (U ∩ xs 0) (Fin.tail xs)]

theorem candidateBlock_zero_expect {n : ℕ} [NeZero n] (k : ℕ)
    (U : Finset (DeletionCandidate n)) (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock 0 k U).expect f = f U := by
  rw [candidateBlock_expect, ProbabilityTheory.integral_poissonMeasure]
  simp [zero_pow_eq, ite_div, ite_mul]

theorem maskLifetime_mean {n : ℕ} [NeZero n] (r : ℝ≥0) (k m : ℕ)
    (U : Finset (DeletionCandidate n)) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock r k Finset.univ)).expect
      (maskLifetime m U) =
      ∑ t ∈ Finset.range m, (candidateBlock (r*t) k U).expect candidateAlive := by
  induction m generalizing U with
  | zero => simp [maskLifetime]
  | succ m ih =>
    rw [FiniteLaw.expect_pi_cons]
    simp only [maskLifetime, Fin.cons_zero, Fin.tail_cons, FiniteLaw.expect_add,
      FiniteLaw.expect_const, ih, FiniteLaw.expect_sum]
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, candidateBlock_zero_expect]
    rw [add_comm (candidateAlive U)]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [candidateBlock_mask r k U (fun V => (candidateBlock (r*t) k V).expect candidateAlive)]
    rw [← candidateBlock_comp]
    congr 2
    push_cast
    ring

theorem candidateBlock_kill_antitone {n : ℕ} [NeZero n] (r : ℝ≥0) (k : ℕ)
    {U V : Finset (DeletionCandidate n)} (hVU : V ⊆ U) :
    poissonKillProbability U k r ≤ poissonKillProbability V k r := by
  have h := candidateBlock_expect_mono_state r k candidateAlive_mono hVU
  change (candidateBlock r k V).expect candidateAlive ≤
    (candidateBlock r k U).expect candidateAlive at h
  rw [candidateBlock_expect_alive, candidateBlock_expect_alive] at h
  linarith

theorem maskLifetime_mean_le {n : ℕ} [NeZero n] (r : ℝ≥0) (k m L : ℕ)
    (U : Finset (DeletionCandidate n)) {δ : ℝ} (hδ : 0 < δ)
    (hkill : δ ≤ poissonKillProbability U k (r*L)) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock r k Finset.univ)).expect
      (maskLifetime m U) ≤ (L : ℝ)/δ := by
  let bin := fun V : Finset (DeletionCandidate n) => V.Nonempty ∧ V ⊆ U
  have hb (V : Finset (DeletionCandidate n)) (hV : bin V) :
      V.Nonempty ∧ δ ≤ poissonKillProbability V k (r*L) :=
    ⟨hV.1, hkill.trans (candidateBlock_kill_antitone _ _ hV.2)⟩
  have he (t : ℕ) : (candidateBlock (r*t) k U).expect candidateAlive =
      (candidateBlock (r*t) k U).expect (fun V => if bin V then 1 else 0) := by
    apply le_antisymm
    · apply candidateBlock_expect_le_of_subset
      intro V hV
      by_cases hne : V.Nonempty <;> simp [candidateAlive, bin, hne, hV]
    · apply candidateBlock_expect_le_of_subset
      intro V hV
      by_cases hne : V.Nonempty <;> simp [candidateAlive, bin, hne, hV]
  rw [maskLifetime_mean]
  simp_rw [he]
  exact candidateBlock_occupation r k L m bin hδ hb U

theorem maskLifetime_fractional_moment {n : ℕ} [NeZero n] (r : ℝ≥0) (k m L : ℕ)
    (U : Finset (DeletionCandidate n)) {δ : ℝ} (hδ : 0 < δ)
    (hkill : δ ≤ poissonKillProbability U k (r*L)) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock r k Finset.univ)).expect
      (fun xs => (maskLifetime m U xs)^(1/5 : ℝ)) ≤ ((L : ℝ)/δ)^(1/5 : ℝ) := by
  apply (finite_fractional_moment _ _ (maskLifetime_nonneg U)).trans
  apply Real.rpow_le_rpow (FiniteLaw.expect_nonneg _ (maskLifetime_nonneg U))
    (maskLifetime_mean_le r k m L U hδ hkill) (by norm_num)

end FixedClauseThreshold.Computability

end OAI
