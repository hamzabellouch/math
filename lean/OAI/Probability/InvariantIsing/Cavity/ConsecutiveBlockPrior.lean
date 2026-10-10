import OAI.Probability.InvariantIsing.Cavity.RepeatedBlockPrior

namespace OAI

/-! Repeated identical cavity constraints admit every even permutation
of their blocks. No coordinate sign flip is introduced. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def consecutiveBlockConstraint (n K : ℕ) (C : Finset (Spin n)) : Finset (Spin (K*n)) :=
  Finset.univ.filter (fun σ => ∀ b : Fin K, (fun i : Fin n => σ (finProdFinEquiv (b,i))) ∈ C)

lemma mem_consecutiveBlockConstraint {n K : ℕ} (C : Finset (Spin n)) (σ : Spin (K*n)) :
    σ ∈ consecutiveBlockConstraint n K C ↔
      ∀ b : Fin K, (fun i : Fin n => σ (finProdFinEquiv (b,i))) ∈ C := by
  simp [consecutiveBlockConstraint]

lemma consecutiveBlockConstraint_nonempty {n K : ℕ} (C : Finset (Spin n)) (hC : C.Nonempty) :
    (consecutiveBlockConstraint n K C).Nonempty := by
  obtain ⟨τ,hτ⟩ := hC
  refine ⟨fun i => τ (finProdFinEquiv.symm i).2, ?_⟩
  rw [mem_consecutiveBlockConstraint]
  intro b
  simpa using hτ

def consecutiveBlockSitePermutation {n K : ℕ} (p : Equiv.Perm (Fin K)) : Equiv.Perm (Fin (K*n)) :=
  finProdFinEquiv.permCongr (Equiv.prodCongrLeft (fun _ : Fin n => p))

lemma consecutiveBlockSitePermutation_apply {n K : ℕ} (p : Equiv.Perm (Fin K))
    (i : Fin n) (b : Fin K) :
    consecutiveBlockSitePermutation p (finProdFinEquiv (b,i)) = finProdFinEquiv (p b,i) := by
  simp [consecutiveBlockSitePermutation]

lemma consecutiveBlockSitePermutation_sign {n K : ℕ} (p : Equiv.Perm (Fin K))
    (hp : Equiv.Perm.sign p = 1) :
    Equiv.Perm.sign (consecutiveBlockSitePermutation (n := n) p) = 1 := by
  simp [consecutiveBlockSitePermutation, Equiv.Perm.sign_prodCongrLeft, hp]

lemma consecutiveBlockSitePermutation_flip {n K : ℕ} (hN : 0 < K*n)
    (p : Equiv.Perm (Fin K)) (hp : Equiv.Perm.sign p = 1) (i : Fin (K*n)) :
    cavityPermutationFlip hN (consecutiveBlockSitePermutation p) i = false := by
  have hs := consecutiveBlockSitePermutation_sign (n := n) p hp
  norm_num [cavityPermutationFlip, Matrix.det_permutation, hs]

lemma consecutiveBlockConstraint_permutation {n K : ℕ} (hN : 0 < K*n)
    (C : Finset (Spin n)) (p : Equiv.Perm (Fin K)) (hp : Equiv.Perm.sign p = 1)
    (σ : Spin (K*n)) :
    cavitySignedSpinPermutation (consecutiveBlockSitePermutation p)
      (cavityPermutationFlip hN (consecutiveBlockSitePermutation p)) σ ∈ consecutiveBlockConstraint n K C ↔
      σ ∈ consecutiveBlockConstraint n K C := by
  simp only [mem_consecutiveBlockConstraint]
  have he (b : Fin K) : (fun i : Fin n =>
      cavitySignedSpinPermutation (consecutiveBlockSitePermutation p)
        (cavityPermutationFlip hN (consecutiveBlockSitePermutation p)) σ (finProdFinEquiv (b,i))) =
      (fun i : Fin n => σ (finProdFinEquiv (p b,i))) := by
    funext i
    change (if cavityPermutationFlip hN (consecutiveBlockSitePermutation p) _ then _ else _) = _
    rw [consecutiveBlockSitePermutation_flip hN p hp]
    simp only [Bool.false_eq_true, ↓reduceIte, consecutiveBlockSitePermutation_apply]
  simp_rw [he]
  constructor
  · intro h b
    simpa using h (p.symm b)
  · intro h b
    exact h (p b)

theorem consecutiveBlockPrior_permutation {n K : ℕ} (hN : 0 < K*n)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (p : Equiv.Perm (Fin K)) (hp : Equiv.Perm.sign p = 1) :
    MeasurePreserving
      (cavitySignedSpinPermutation (consecutiveBlockSitePermutation p)
        (cavityPermutationFlip hN (consecutiveBlockSitePermutation p)))
      (restrictedSpinPrior (consecutiveBlockConstraint n K C) (consecutiveBlockConstraint_nonempty C hC) :
        Measure (Spin (K*n)))
      (restrictedSpinPrior (consecutiveBlockConstraint n K C) (consecutiveBlockConstraint_nonempty C hC) :
        Measure (Spin (K*n))) :=
  restrictedSpinPrior_equiv _ _ _ (consecutiveBlockConstraint_permutation hN C p hp)

end InvariantIsing

end

end OAI
