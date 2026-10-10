import OAI.RepresentationTheory.FoulkesHowe.Model

namespace OAI

noncomputable section

open scoped BigOperators
universe u

namespace Problem346

/-- Reindexing the factors of a symmetric monomial does not change it. -/
theorem symMonomial_perm_reindex (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin n → V)
    (τ : Equiv.Perm (Fin n)) :
    symMonomial n V (fun i => v (τ i)) = symMonomial n V v := by
  apply Subtype.ext
  exact Equiv.prod_comp τ (fun i => SymmetricAlgebra.ι ℂ V (v i))

/-- The canonical averaging formula is invariant under independent permutations
of the entries in each row. -/
theorem foulkesFormula_inner_permute (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin a → V)
    (τ : Fin b → Equiv.Perm (Fin a)) :
    foulkesFormula a b V (fun j i => v j (τ j i)) =
      foulkesFormula a b V v := by
  classical
  unfold foulkesFormula
  congr 1
  exact Fintype.sum_equiv
    (Equiv.piCongrRight (fun j => Equiv.mulLeft (τ j))) _ _ (fun σ => rfl)

/-- The canonical averaging formula is invariant under permutation of rows. -/
theorem foulkesFormula_outer_permute (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin a → V)
    (τ : Equiv.Perm (Fin b)) :
    foulkesFormula a b V (fun j i => v (τ j) i) =
      foulkesFormula a b V v := by
  classical
  unfold foulkesFormula
  congr 1
  apply Fintype.sum_equiv (Equiv.arrowCongr τ (Equiv.refl (Equiv.Perm (Fin a))))
  intro σ
  congr 1
  funext i
  simpa using symMonomial_perm_reindex b V
    (fun j => v j (σ (τ.symm j) i)) τ

end Problem346

end

end OAI
