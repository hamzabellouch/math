import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinSymmetry

namespace OAI

/-! Repeated identical cavity constraints admit every even permutation
of their blocks. No coordinate sign flip is introduced. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def spinBlockConstraint (n K : ℕ) (C : Finset (Spin n)) : Finset (Spin (n*K)) :=
  Finset.univ.filter (fun σ => ∀ b : Fin K, (fun i : Fin n => σ (finProdFinEquiv (i,b))) ∈ C)

lemma mem_spinBlockConstraint {n K : ℕ} (C : Finset (Spin n)) (σ : Spin (n*K)) :
    σ ∈ spinBlockConstraint n K C ↔
      ∀ b : Fin K, (fun i : Fin n => σ (finProdFinEquiv (i,b))) ∈ C := by
  simp [spinBlockConstraint]

lemma spinBlockConstraint_nonempty {n K : ℕ} (C : Finset (Spin n)) (hC : C.Nonempty) :
    (spinBlockConstraint n K C).Nonempty := by
  obtain ⟨τ,hτ⟩ := hC
  refine ⟨fun i => τ (finProdFinEquiv.symm i).1, ?_⟩
  rw [mem_spinBlockConstraint]
  intro b
  simpa using hτ

def spinBlockSitePermutation {n K : ℕ} (p : Equiv.Perm (Fin K)) : Equiv.Perm (Fin (n*K)) :=
  finProdFinEquiv.permCongr (Equiv.prodCongrRight (fun _ : Fin n => p))

lemma spinBlockSitePermutation_apply {n K : ℕ} (p : Equiv.Perm (Fin K))
    (i : Fin n) (b : Fin K) :
    spinBlockSitePermutation p (finProdFinEquiv (i,b)) = finProdFinEquiv (i,p b) := by
  simp [spinBlockSitePermutation]

lemma spinBlockSitePermutation_sign {n K : ℕ} (p : Equiv.Perm (Fin K))
    (hp : Equiv.Perm.sign p = 1) :
    Equiv.Perm.sign (spinBlockSitePermutation (n := n) p) = 1 := by
  simp [spinBlockSitePermutation, Equiv.Perm.sign_prodCongrRight, hp]

lemma spinBlockSitePermutation_flip {n K : ℕ} (hN : 0 < n*K)
    (p : Equiv.Perm (Fin K)) (hp : Equiv.Perm.sign p = 1) (i : Fin (n*K)) :
    cavityPermutationFlip hN (spinBlockSitePermutation p) i = false := by
  have hs := spinBlockSitePermutation_sign (n := n) p hp
  norm_num [cavityPermutationFlip, Matrix.det_permutation, hs]

lemma spinBlockConstraint_permutation {n K : ℕ} (hN : 0 < n*K)
    (C : Finset (Spin n)) (p : Equiv.Perm (Fin K)) (hp : Equiv.Perm.sign p = 1)
    (σ : Spin (n*K)) :
    cavitySignedSpinPermutation (spinBlockSitePermutation p)
      (cavityPermutationFlip hN (spinBlockSitePermutation p)) σ ∈ spinBlockConstraint n K C ↔
      σ ∈ spinBlockConstraint n K C := by
  simp only [mem_spinBlockConstraint]
  have he (b : Fin K) : (fun i : Fin n =>
      cavitySignedSpinPermutation (spinBlockSitePermutation p)
        (cavityPermutationFlip hN (spinBlockSitePermutation p)) σ (finProdFinEquiv (i,b))) =
      (fun i : Fin n => σ (finProdFinEquiv (i,p b))) := by
    funext i
    change (if cavityPermutationFlip hN (spinBlockSitePermutation p) _ then _ else _) = _
    rw [spinBlockSitePermutation_flip hN p hp]
    simp only [Bool.false_eq_true, ↓reduceIte, spinBlockSitePermutation_apply]
  simp_rw [he]
  constructor
  · intro h b
    simpa using h (p.symm b)
  · intro h b
    exact h (p b)

theorem repeatedBlockPrior_permutation {n K : ℕ} (hN : 0 < n*K)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (p : Equiv.Perm (Fin K)) (hp : Equiv.Perm.sign p = 1) :
    MeasurePreserving
      (cavitySignedSpinPermutation (spinBlockSitePermutation p)
        (cavityPermutationFlip hN (spinBlockSitePermutation p)))
      (restrictedSpinPrior (spinBlockConstraint n K C) (spinBlockConstraint_nonempty C hC) :
        Measure (Spin (n*K)))
      (restrictedSpinPrior (spinBlockConstraint n K C) (spinBlockConstraint_nonempty C hC) :
        Measure (Spin (n*K))) :=
  restrictedSpinPrior_equiv _ _ _ (spinBlockConstraint_permutation hN C p hp)

lemma even_block_permutation {K : ℕ} (hK : 3 ≤ K) (i j : Fin K) :
    ∃ p : Equiv.Perm (Fin K), Equiv.Perm.sign p = 1 ∧ p i = j := by
  by_cases hij : i = j
  · subst j
    exact ⟨1, by simp, by simp⟩
  have hk : ∃ k : Fin K, k ≠ i ∧ k ≠ j := by
    by_contra! h
    have hs : (Finset.univ : Finset (Fin K)) ⊆ {i,j} := by
      intro k _
      have he : k = i ∨ k = j := by
        by_cases hi : k = i
        · exact Or.inl hi
        · exact Or.inr (h k hi)
      simpa using he
    have hc := Finset.card_le_card hs
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_pair hij] at hc
    omega
  obtain ⟨k,hki,hkj⟩ := hk
  refine ⟨Equiv.swap j k * Equiv.swap i k, ?_, ?_⟩
  · rw [map_mul, Equiv.Perm.sign_swap hkj.symm, Equiv.Perm.sign_swap hki.symm]
    norm_num
  · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]

end InvariantIsing

end

end OAI
