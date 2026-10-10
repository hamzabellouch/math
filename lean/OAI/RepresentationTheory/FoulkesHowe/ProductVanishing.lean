import OAI.RepresentationTheory.FoulkesHowe.VanishingFirst
import OAI.RepresentationTheory.FoulkesHowe.SecondTransfer

namespace OAI

noncomputable section

namespace Problem346

universe u

/-- Quadratic stabilization of diagonal vanishing on products. Both differential
transfers and all of the induction hypotheses are discharged in this theorem. -/
theorem vanishing_on_products_aux (V : Type u)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a*(a-1) ≤ b)
    (T : SymmetricMultilinearForm a b V)
    (hT : IsSymmetricMultilinearForm a b V T)
    (hdiag : ∀ y : Fin b → V, T (fun _ => symMonomial b V y) = 0) : T = 0 := by
  refine vanishing_on_products_of_second_transfer (V := V) ?_ a b ha hb hab T hT hdiag
  intro r m _ _ hbound S _ hrest
  exact SecondTransfer.second_transfer r m (by simpa only [Nat.mul_comm] using hbound) S hrest

end Problem346

end

end OAI
