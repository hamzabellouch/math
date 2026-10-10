import OAI.Probability.SATComputability.MaskPermutations
import OAI.Probability.SATComputability.GridBlockLaw

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped NNReal Classical

theorem maskGrid_permutation {n k M : ℕ} (e : Equiv.Perm (Fin n))
    (c : (Fin k → SignedLiteral n) × Fin M → ℕ) :
    (fun j => renameMask e (maskGrid clauseMask c j)) =
      maskGrid clauseMask (fun p => c ((clausePermutation e k).symm p.1,p.2)) := by
  funext j
  exact countsMask_permutation e (fun a => c (a,j))

theorem gridMaskLaw_permutation {n k M : ℕ} (e : Equiv.Perm (Fin n)) (r : ℝ≥0)
    (f : (Fin M → Finset (DeletionCandidate n)) → ℝ) :
    (gridMaskLaw M r (clauseMask (n := n) (k := k))).expect
      (fun xs => f (fun j => renameMask e (xs j))) =
      (gridMaskLaw M r (clauseMask (n := n) (k := k))).expect f := by
  simp only [gridMaskLaw_expect, maskGrid_permutation]
  have h := poissonCountLaw_equiv
    ((clausePermutation e k).prodCongr (Equiv.refl (Fin M))) r
    (fun c => f (maskGrid clauseMask c))
  exact h

theorem candidatePath_permutation {n : ℕ} [NeZero n] (M k : ℕ)
    (e : Equiv.Perm (Fin n)) (r : ℝ≥0)
    (f : (Fin M → Finset (DeletionCandidate n)) → ℝ) :
    (FiniteLaw.pi (fun _ : Fin M => candidateBlock r k Finset.univ)).expect
      (fun xs => f (fun j => renameMask e (xs j))) =
      (FiniteLaw.pi (fun _ : Fin M => candidateBlock r k Finset.univ)).expect f := by
  have hc : (Fintype.card (Fin k → SignedLiteral n) : ℝ≥0) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h := gridMaskLaw_permutation (k := k) (M := M) e
    (r/Fintype.card (Fin k → SignedLiteral n)) f
  rw [gridMaskLaw_clauses, div_mul_cancel₀ _ hc] at h
  exact h

end FixedClauseThreshold.Computability

end OAI
