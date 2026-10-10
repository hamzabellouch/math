import OAI.Probability.SATComputability.RestoredCandidates
import OAI.Probability.SATComputability.UniformDelayConstant

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical NNReal

theorem mem_maskRun {n m : ℕ} (U : Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) (x : DeletionCandidate n) :
    x ∈ maskRun m U xs ↔ x ∈ U ∧ ∀ j, x ∈ xs j := by
  induction m generalizing U with
  | zero => simp [maskRun]
  | succ m ih =>
    simp only [maskRun, ih, Finset.mem_inter, Fin.forall_fin_succ, Fin.tail_def, and_assoc]

noncomputable def frontloadMask {n m : ℕ} (xs : Fin m → Finset (DeletionCandidate n)) :
    Finset (DeletionCandidate n) := maskRun m Finset.univ xs

theorem frontloadMask_subset {n m : ℕ} (xs : Fin m → Finset (DeletionCandidate n))
    (j : Fin m) : frontloadMask xs ⊆ xs j := by
  intro x hx
  exact (mem_maskRun _ xs x).mp hx |>.2 j

theorem restored_process_moment {n : ℕ} [NeZero n] (M r : ℕ)
    (rate : ℝ≥0) (hrate : (1 : ℝ)/8 ≤ rate)
    (P : FiniteLaw (Fin M → Finset (DeletionCandidate n))) (ε : ℝ)
    (hP : ∀ U, (finiteMap P frontloadMask).expect
      (fun I => if U ∩ I = ∅ then 1 else 0) ≤ poissonKillProbability U 2 60 + ε) :
    P.expect (fun f => P.expect (fun t =>
      (FiniteLaw.pi (fun _ : Fin M => candidateBlock rate 3 Finset.univ)).expect (fun base =>
        (maskLifetime M (deletionBudgetMask n r) base -
          maskLifetime M (deletionBudgetMask (n+1) r)
            (fun j => restoredMask (base j) (f j) (t j)))^(6/5 : ℝ)))) ≤
      (48/5 : ℝ)*(∑' j, dyadicMomentCoefficient j) +
        (12/5 : ℝ)*ε^2*(M : ℝ)^(6/5 : ℝ) := by
  let Q := finiteMap P frontloadMask
  have hQ (U : Finset (DeletionCandidate n)) :
      (unionMaskLaw Q Q).expect (fun I => if U.Nonempty ∧ U ∩ I = ∅ then 1 else 0) ≤
        (poissonKillProbability U 2 60 + ε)^2 := by
    by_cases hU : U.Nonempty
    · simp only [hU, true_and, unionMaskLaw_killing]
      rw [← pow_two]
      exact pow_le_pow_left₀ (FiniteLaw.expect_nonneg _ (fun I => by split_ifs <;> norm_num))
        (hP U) 2
    · simp only [hU, false_and, ite_false, FiniteLaw.expect_const]
      exact sq_nonneg _
  have h := maskDelayMoment_of_obstruction rate hrate M (unionMaskLaw Q Q) ε hQ
    (deletionBudgetMask n r)
  apply le_trans ?_ h
  rw [unionMaskLaw, finiteMap_expect, FiniteLaw.expect_bind]
  simp only [Q, finiteMap_expect]
  apply P.expect_mono
  intro f
  apply P.expect_mono
  intro t
  exact FiniteLaw.expect_mono _ (fun base =>
    restored_gap_bound base f t (frontloadMask f) (frontloadMask t)
      (frontloadMask_subset f) (frontloadMask_subset t))

end FixedClauseThreshold.Computability

end OAI
