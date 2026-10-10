import OAI.Probability.InvariantIsing.Cavity.ConsecutiveBlockSplit

namespace OAI

/-! Even block permutations act on the exact base/cavity product slice. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def consecutiveProductSite (n K : ℕ) (b : Fin (K+1)) (i : Fin n) : Fin (K*n+n) :=
  Fin.cast (Nat.succ_mul K n) (finProdFinEquiv (b,i))

lemma consecutiveProductSite_injective {n K : ℕ} (i : Fin n) :
    Function.Injective (fun b : Fin (K+1) => consecutiveProductSite n K b i) := by
  intro b c h
  have hpair := finProdFinEquiv.injective (Fin.cast_injective _ h)
  exact congrArg Prod.fst hpair

lemma consecutiveProductSite_last {n K : ℕ} (i : Fin n) :
    consecutiveProductSite n K (Fin.last K) i = Fin.natAdd (K*n) i := by
  apply Fin.ext
  change i.val + n*K = K*n+i.val
  simp [Nat.mul_comm, Nat.add_comm]

def consecutiveProductSitePermutation {n K : ℕ} (p : Equiv.Perm (Fin (K+1))) :
    Equiv.Perm (Fin (K*n+n)) :=
  (finCongr (Nat.succ_mul K n)).permCongr (consecutiveBlockSitePermutation (n := n) p)

lemma consecutiveProductSitePermutation_apply {n K : ℕ}
    (p : Equiv.Perm (Fin (K+1))) (i : Fin n) (b : Fin (K+1)) :
    consecutiveProductSitePermutation p (consecutiveProductSite n K b i) =
      consecutiveProductSite n K (p b) i := by
  simp [consecutiveProductSitePermutation, consecutiveProductSite,
    consecutiveBlockSitePermutation_apply]

lemma consecutiveProductSitePermutation_sign {n K : ℕ}
    (p : Equiv.Perm (Fin (K+1))) (hp : Equiv.Perm.sign p = 1) :
    Equiv.Perm.sign (consecutiveProductSitePermutation (n := n) p) = 1 := by
  simp [consecutiveProductSitePermutation, consecutiveBlockSitePermutation_sign p hp]

lemma consecutiveProductSitePermutation_flip {n K : ℕ} (hN : 0 < K*n+n)
    (p : Equiv.Perm (Fin (K+1))) (hp : Equiv.Perm.sign p = 1) (i : Fin (K*n+n)) :
    cavityPermutationFlip hN (consecutiveProductSitePermutation p) i = false := by
  have hs := consecutiveProductSitePermutation_sign (n := n) p hp
  norm_num [cavityPermutationFlip, Matrix.det_permutation, hs]

lemma mem_consecutiveProduct {n K : ℕ} (C : Finset (Spin n)) (σ : Spin (K*n+n)) :
    σ ∈ cavityProductSlice (consecutiveBlockConstraint n K C) C ↔
      ∀ b : Fin (K+1), (fun i => σ (consecutiveProductSite n K b i)) ∈ C := by
  rw [← consecutiveBlockJoin_mem, mem_consecutiveBlockConstraint]
  rfl

lemma consecutiveProduct_permutation {n K : ℕ} (hN : 0 < K*n+n)
    (C : Finset (Spin n)) (p : Equiv.Perm (Fin (K+1))) (hp : Equiv.Perm.sign p = 1)
    (σ : Spin (K*n+n)) :
    cavitySignedSpinPermutation (consecutiveProductSitePermutation p)
      (cavityPermutationFlip hN (consecutiveProductSitePermutation p)) σ ∈
        cavityProductSlice (consecutiveBlockConstraint n K C) C ↔
      σ ∈ cavityProductSlice (consecutiveBlockConstraint n K C) C := by
  simp only [mem_consecutiveProduct]
  have he (b : Fin (K+1)) : (fun i : Fin n =>
      cavitySignedSpinPermutation (consecutiveProductSitePermutation p)
        (cavityPermutationFlip hN (consecutiveProductSitePermutation p)) σ
          (consecutiveProductSite n K b i)) =
      (fun i : Fin n => σ (consecutiveProductSite n K (p b) i)) := by
    funext i
    change (if cavityPermutationFlip hN (consecutiveProductSitePermutation p) _ then _ else _) = _
    rw [consecutiveProductSitePermutation_flip hN p hp]
    simp only [Bool.false_eq_true, ↓reduceIte, consecutiveProductSitePermutation_apply]
  simp_rw [he]
  constructor
  · intro h b
    simpa using h (p.symm b)
  · intro h b
    exact h (p b)

end InvariantIsing

end

end OAI
