import OAI.RepresentationTheory.FoulkesHowe.BinaryFactorization
import OAI.RepresentationTheory.FoulkesHowe.DiagonalCoefficient
import OAI.RepresentationTheory.FoulkesHowe.Multiplication

namespace OAI

noncomputable section

namespace Problem346

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The split-pencil consequence of diagonal vanishing, expressed using the
graded multiplication and first-slot convention of the induction. -/
theorem binary_diagonal_to_mixed_products (r m : ℕ) (hr : 0 < r)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (hT : IsSymmetricMultilinearForm (r+1) (r+m) V T)
    (hdiag : ∀ y : Fin (r+m) → V, T (fun _ => symMonomial (r+m) V y) = 0)
    (x t : V) (y : Fin m → V) :
    T (Fin.cons
      (symPowMul r m (symMonomial r V (fun _ => t)) (symMonomial m V y))
      (fun _ : Fin r =>
        symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) = 0 := by
  apply symmetric_diagonal_cons_zero T hT
  intro c
  obtain ⟨v, hv⟩ := symMonomial_binary_power_mul V r m hr x t c y
  simp only [symPowMul_symMonomial]
  rw [← hv]
  exact hdiag v

end Problem346

end

end OAI
