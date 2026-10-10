import OAI.Analysis.BoundedHochschild.ScalarMatrixActions

namespace OAI

/-! Exchange the finite matrix indices in a two-by-two amplification. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A]

def flipMatrixNesting (n k : ℕ) :
    CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin k) (Fin k) A) ≃⋆ₐ[ℂ]
      CStarMatrix (Fin k) (Fin k) (CStarMatrix (Fin n) (Fin n) A) where
  toFun X i j p q := X p q i j
  invFun X i j p q := X p q i j
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl
  map_mul' X Y := by
    ext i j p q
    change (∑ s : Fin n, (fun r t => ∑ l : Fin k, X p s r l * Y s q l t)) i j =
      (∑ l : Fin k, (fun r t => ∑ s : Fin n, X r s i l * Y s t l j)) p q
    simp only [Finset.sum_apply]
    exact Finset.sum_comm

@[simp] lemma flipMatrixNesting_apply (n k : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin k) (Fin k) A))
    (i j : Fin k) (p q : Fin n) : flipMatrixNesting n k X i j p q = X p q i j := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
