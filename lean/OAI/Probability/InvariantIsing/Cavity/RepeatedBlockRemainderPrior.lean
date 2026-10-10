import OAI.Probability.InvariantIsing.Cavity.RepeatedBlockPrior
import OAI.Probability.InvariantIsing.Magnetic.RestrictedProductPrior

namespace OAI

/-! Even block permutations preserve repeated constraints and an
arbitrary fixed remainder constraint. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def blockRemainderSitePermutation {n K r : ℕ} (p : Equiv.Perm (Fin K)) :
    Equiv.Perm (Fin (n*K+r)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr (spinBlockSitePermutation (n := n) p) (Equiv.refl (Fin r)))

lemma blockRemainderSitePermutation_left {n K r : ℕ} (p : Equiv.Perm (Fin K))
    (i : Fin (n*K)) :
    blockRemainderSitePermutation p (Fin.castAdd r i) = Fin.castAdd r (spinBlockSitePermutation p i) := by
  simp [blockRemainderSitePermutation]

lemma blockRemainderSitePermutation_right {n K r : ℕ} (p : Equiv.Perm (Fin K))
    (i : Fin r) :
    blockRemainderSitePermutation (n := n) p (Fin.natAdd (n*K) i) = Fin.natAdd (n*K) i := by
  simp [blockRemainderSitePermutation]

lemma blockRemainderSitePermutation_sign {n K r : ℕ} (p : Equiv.Perm (Fin K))
    (hp : Equiv.Perm.sign p = 1) :
    Equiv.Perm.sign (blockRemainderSitePermutation (n := n) (r := r) p) = 1 := by
  simp [blockRemainderSitePermutation, Equiv.Perm.sign_sumCongr, spinBlockSitePermutation_sign p hp]

lemma cavityPermutationFlip_eq_false_of_sign {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (hp : Equiv.Perm.sign p = 1) (i : Fin N) :
    cavityPermutationFlip hN p i = false := by
  norm_num [cavityPermutationFlip, Matrix.det_permutation, hp]

theorem block_remainder_constraint_permutation {n K r : ℕ} (hN : 0 < n*K)
    (C : Finset (Spin n)) (R : Finset (Spin r))
    (p : Equiv.Perm (Fin K)) (hp : Equiv.Perm.sign p = 1) (σ : Spin (n*K+r)) :
    cavitySignedSpinPermutation (blockRemainderSitePermutation p)
      (cavityPermutationFlip (Nat.add_pos_left hN r) (blockRemainderSitePermutation p)) σ ∈
        cavityProductSlice (spinBlockConstraint n K C) R ↔
      σ ∈ cavityProductSlice (spinBlockConstraint n K C) R := by
  let f := cavitySignedSpinPermutation (blockRemainderSitePermutation (n := n) (r := r) p)
    (cavityPermutationFlip (Nat.add_pos_left hN r) (blockRemainderSitePermutation p))
  have hl : (cavitySpinSplit (n*K) r (f σ)).1 =
      cavitySignedSpinPermutation (spinBlockSitePermutation p)
        (cavityPermutationFlip hN (spinBlockSitePermutation p)) (cavitySpinSplit (n*K) r σ).1 := by
    funext i
    change (if cavityPermutationFlip _ _ _ then _ else _) =
      (if cavityPermutationFlip _ _ _ then _ else _)
    rw [cavityPermutationFlip_eq_false_of_sign _ _ (blockRemainderSitePermutation_sign p hp),
      spinBlockSitePermutation_flip hN p hp]
    simp only [Bool.false_eq_true, ↓reduceIte, blockRemainderSitePermutation_left]
    rfl
  have hr : (cavitySpinSplit (n*K) r (f σ)).2 = (cavitySpinSplit (n*K) r σ).2 := by
    funext i
    change (if cavityPermutationFlip _ _ _ then _ else _) = _
    rw [cavityPermutationFlip_eq_false_of_sign _ _ (blockRemainderSitePermutation_sign p hp)]
    simp only [Bool.false_eq_true, ↓reduceIte, blockRemainderSitePermutation_right]
    rfl
  change f σ ∈ _ ↔ _
  simp only [mem_cavityProductSlice, hl, hr, spinBlockConstraint_permutation hN C p hp]

end InvariantIsing

end

end OAI
