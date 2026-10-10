import OAI.Probability.SATComputability.CandidateSurvival

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory
open scoped NNReal Classical

theorem candidateResidual_inter {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (cs : Fin d → Fin k → SignedLiteral n) :
    candidateResidual U cs = U ∩ candidateResidual Finset.univ cs := by
  ext x
  simp only [candidateResidual, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]

theorem candidateFixedBlock_mask {n : ℕ} [NeZero n] (k d : ℕ)
    (U : Finset (DeletionCandidate n)) (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateFixedBlock k d Finset.univ).expect (fun V => f (U ∩ V)) =
      (candidateFixedBlock k d U).expect f := by
  simp only [candidateFixedBlock_expect, candidateStep_iterate]
  apply FiniteLaw.expect_congr
  intro cs
  rw [candidateResidual_inter U cs]

theorem candidateBlock_mask {n : ℕ} [NeZero n] (r : ℝ≥0) (k : ℕ)
    (U : Finset (DeletionCandidate n)) (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock r k Finset.univ).expect (fun V => f (U ∩ V)) =
      (candidateBlock r k U).expect f := by
  simp only [candidateBlock, poissonMixture_expect, candidateFixedBlock_mask]

noncomputable def maskRun {n : ℕ} : (m : ℕ) → Finset (DeletionCandidate n) →
    (Fin m → Finset (DeletionCandidate n)) → Finset (DeletionCandidate n)
  | 0, U, _ => U
  | m+1, U, xs => maskRun m (U ∩ xs 0) (Fin.tail xs)

theorem maskRun_law {n : ℕ} [NeZero n] (r : ℝ≥0) (k m : ℕ)
    (U : Finset (DeletionCandidate n)) (f : Finset (DeletionCandidate n) → ℝ) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock r k Finset.univ)).expect
      (fun xs => f (maskRun m U xs)) = (candidateBlock (r*m) k U).expect f := by
  induction m generalizing U with
  | zero =>
    simp only [maskRun, FiniteLaw.expect_const, Nat.cast_zero, mul_zero]
    rw [candidateBlock_expect, integral_poissonMeasure]
    simp [zero_pow_eq, ite_div, ite_mul]
  | succ m ih =>
    rw [FiniteLaw.expect_pi_cons]
    simp only [maskRun, Fin.cons_zero, Fin.tail_cons, ih]
    rw [candidateBlock_mask r k U (fun V => (candidateBlock (r*m) k V).expect f)]
    rw [← candidateBlock_comp]
    congr 2
    push_cast
    ring

end FixedClauseThreshold.Computability

end OAI
