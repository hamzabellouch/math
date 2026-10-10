import OAI.RepresentationTheory.FoulkesHowe.Vanishing
import OAI.RepresentationTheory.FoulkesHowe.BinaryVanishing
import OAI.RepresentationTheory.FoulkesHowe.FirstTransfer
import OAI.RepresentationTheory.FoulkesHowe.PowerSpan

namespace OAI

noncomputable section

namespace Problem346

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Diagonal vanishing gives the diagonal vanishing of the lower-arity form.
This combines binary splitting, coefficient extraction, and the first transfer. -/
theorem lowerProductForm_diagonal_zero (r m : ℕ) (hr : 0 < r)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (hT : IsSymmetricMultilinearForm (r+1) (r+m) V T)
    (hdiag : ∀ y : Fin (r+m) → V, T (fun _ => symMonomial (r+m) V y) = 0)
    (x t : V) (y : Fin m → V) :
    lowerProductForm r m T x t (fun _ => symMonomial m V y) = 0 := by
  exact first_transfer T (binary_diagonal_to_mixed_products r m hr T hT hdiag) x t y

/-- With the first transfer and pure-power detection established, the common-power
removal transfer is the sole remaining input to the vanishing induction. -/
theorem vanishing_on_products_of_second_transfer
    (secondTransfer : ∀ r m : ℕ, 0 < r → 0 < m → (r+1)*r ≤ r+m →
      ∀ T : SymmetricMultilinearForm (r+1) (r+m) V,
      IsSymmetricMultilinearForm (r+1) (r+m) V T →
      (∀ x t : V, ∀ Q : Fin r → SymPow m V, lowerProductForm r m T x t Q = 0) →
      ∀ v : Fin (r+1) → V,
        T (fun i => symMonomial (r+m) V (fun _ => v i)) = 0) :
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a*(a-1) ≤ b →
      ∀ T : SymmetricMultilinearForm a b V,
      IsSymmetricMultilinearForm a b V T →
      (∀ y : Fin b → V, T (fun _ => symMonomial b V y) = 0) → T = 0 := by
  apply vanishing_induction_from_transfer_steps
  · intro r m hr _ _ T hT hdiag
    exact lowerProductForm_diagonal_zero r m hr T hT hdiag
  · exact secondTransfer
  · intro a b T hT
    exact symmetricMultilinearForm_eq_zero_of_pure_powers a b V T hT

end Problem346

end

end OAI
