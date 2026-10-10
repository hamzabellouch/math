import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDigitAverages

namespace OAI

/-! # Transposing all block-prime patterns to their endpoint types -/

namespace JointDickman
open Finset Classical PublishedInputs

noncomputable def univPiEquiv (α β : Type*) [Fintype α] :
    (↥(univ : Finset α) → β) ≃ (α → β) where
  toFun f a := f ⟨a,mem_univ a⟩
  invFun f a := f a.val
  left_inv f := by funext a; rfl
  right_inv f := rfl

noncomputable def blockPatternEquiv (B M : ℕ) :
    BlockPrimePatterns B M ≃ (Fin M → (auxiliaryPrimes B).powerset) :=
  (primeSiteTranspose (univ : Finset (Fin M)) (auxiliaryPrimes B)).trans
    (univPiEquiv (Fin M) ((auxiliaryPrimes B).powerset))

theorem blockPatternEquiv_val {B M : ℕ} (H : BlockPrimePatterns B M) (i : Fin M) :
    (blockPatternEquiv B M H i).val = primePatternsSites H i := rfl

theorem blockPatternEquiv_mass {B M : ℕ} (H : BlockPrimePatterns B M) :
    bernoulliProductMass univ
      (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) H =
    siteProductMass (fun _ : Fin M => independentPrimeSetMass B) (blockPatternEquiv B M H) := by
  rw [primeSiteTranspose_mass univ (auxiliaryPrimes B) (fun p : ℕ => 1/(p : ℝ)) H]
  change (∏ i : (univ : Finset (Fin M)),
    independentPrimeSetMass B (blockPatternEquiv B M H i.val)) =
      ∏ i : Fin M, independentPrimeSetMass B (blockPatternEquiv B M H i)
  exact (univ : Finset (Fin M)).prod_coe_sort
    (fun i => independentPrimeSetMass B (blockPatternEquiv B M H i))

theorem blockPatternEquiv_sum {B M : ℕ}
    (F : (Fin M → (auxiliaryPrimes B).powerset) → ℝ) :
    (∑ H : BlockPrimePatterns B M, bernoulliProductMass univ
      (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) H *
        F (blockPatternEquiv B M H)) =
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B)) F := by
  simp only [blockPatternEquiv_mass]
  exact (blockPatternEquiv B M).sum_comp
    (fun S => siteProductMass (fun _ : Fin M => independentPrimeSetMass B) S * F S)

end JointDickman

end OAI
