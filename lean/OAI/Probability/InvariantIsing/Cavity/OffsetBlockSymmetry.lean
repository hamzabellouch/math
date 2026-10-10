import OAI.Probability.InvariantIsing.Cavity.OffsetBlockPrior
import OAI.Probability.InvariantIsing.Cavity.RepeatedBlockRemainderPrior

namespace OAI

/-! Even permutations of the repeated blocks preserve an arbitrary initial remainder. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def offsetBlockSitePermutation {r n K : ℕ} (p : Equiv.Perm (Fin K)) :
    Equiv.Perm (Fin (r+K*n)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin r))
    (consecutiveBlockSitePermutation (n := n) p))

lemma offsetBlockSitePermutation_prefix {r n K : ℕ} (p : Equiv.Perm (Fin K)) (i : Fin r) :
    offsetBlockSitePermutation p (Fin.castAdd (K*n) i)=Fin.castAdd (K*n) i := by
  simp [offsetBlockSitePermutation]

lemma offsetBlockSitePermutation_block {r n K : ℕ} (p : Equiv.Perm (Fin K)) (i : Fin (K*n)) :
    offsetBlockSitePermutation p (Fin.natAdd r i)=Fin.natAdd r (consecutiveBlockSitePermutation p i) := by
  simp [offsetBlockSitePermutation]

lemma offsetBlockSitePermutation_sign {r n K : ℕ} (p : Equiv.Perm (Fin K))
    (hp : Equiv.Perm.sign p=1) :
    Equiv.Perm.sign (offsetBlockSitePermutation (r := r) (n := n) p)=1 := by
  simp [offsetBlockSitePermutation,Equiv.Perm.sign_sumCongr,consecutiveBlockSitePermutation_sign p hp]

lemma offsetBlockConstraint_permutation {r n K : ℕ} (hKn : 0<K*n)
    (R : Finset (Spin r)) (C : Finset (Spin n)) (p : Equiv.Perm (Fin K))
    (hp : Equiv.Perm.sign p=1) (σ : Spin (r+K*n)) :
    cavitySignedSpinPermutation (offsetBlockSitePermutation p)
      (cavityPermutationFlip (Nat.add_pos_right r hKn) (offsetBlockSitePermutation p)) σ ∈
        offsetBlockConstraint K R C ↔ σ∈offsetBlockConstraint K R C := by
  let f := cavitySignedSpinPermutation (offsetBlockSitePermutation (r := r) (n := n) p)
    (cavityPermutationFlip (Nat.add_pos_right r hKn) (offsetBlockSitePermutation p))
  have hl : (cavitySpinSplit r (K*n) (f σ)).1=(cavitySpinSplit r (K*n) σ).1 := by
    funext i
    change (if cavityPermutationFlip _ _ _ then _ else _)=_
    rw [cavityPermutationFlip_eq_false_of_sign _ _ (offsetBlockSitePermutation_sign p hp)]
    simp only [Bool.false_eq_true,↓reduceIte,offsetBlockSitePermutation_prefix]
    rfl
  have hr : (cavitySpinSplit r (K*n) (f σ)).2=
      cavitySignedSpinPermutation (consecutiveBlockSitePermutation p)
        (cavityPermutationFlip hKn (consecutiveBlockSitePermutation p))
        (cavitySpinSplit r (K*n) σ).2 := by
    funext i
    change (if cavityPermutationFlip _ _ _ then _ else _)=(if cavityPermutationFlip _ _ _ then _ else _)
    rw [cavityPermutationFlip_eq_false_of_sign _ _ (offsetBlockSitePermutation_sign p hp),
      consecutiveBlockSitePermutation_flip hKn p hp]
    simp only [Bool.false_eq_true,↓reduceIte,offsetBlockSitePermutation_block]
    rfl
  change f σ∈cavityProductSlice R (consecutiveBlockConstraint n K C) ↔
    σ∈cavityProductSlice R (consecutiveBlockConstraint n K C)
  simp only [mem_cavityProductSlice,hl,hr,consecutiveBlockConstraint_permutation hKn C p hp]

end InvariantIsing

end

end OAI
