import OAI.Algebra.AuslanderReiten.Triangular.ConvertedStructure
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionStructure

namespace OAI

namespace ArExplicit.ConvertedAlgebra

open TensorProduct

variable {k : Type*} [Field k] (q : k) (F : Type*) [AddCommGroup F]
variable [Module (A k q) F] [Module (A k q)ᵐᵒᵖ F]
variable [SMulCommClass (A k q) (A k q)ᵐᵒᵖ F]
variable [Module k F]
variable [IsScalarTower k (A k q) F] [IsScalarTower k (A k q)ᵐᵒᵖ F]
variable [SMulCommClass k (A k q) F] [SMulCommClass k (A k q)ᵐᵒᵖ F]

noncomputable def diagonalAlg : ConvertedAlgebra k q F →ₐ[k] (Fin 8 → k) :=
  (eightCoordinates k).toAlgHom.comp (Triangular.quotientMap (F := F) k (A.diagonalAlg q))

theorem diagonalAlg_surjective : Function.Surjective (diagonalAlg q F) :=
  (eightCoordinates k).surjective.comp
    (Triangular.quotientMap_surjective k (A.diagonalAlg q) (A.diagonalAlg_surjective q))

theorem radical_eq_ker_diagonal :
    Ring.jacobson (ConvertedAlgebra k q F) = RingHom.ker (diagonalAlg q F) := by
  rw [Triangular.radical_eq_ker_quotientMap k (A.diagonalAlg q) (A.radical_eq_ker_diagonal q)]
  ext a
  change Triangular.quotientMap k (A.diagonalAlg q) a = 0 ↔
    eightCoordinates k (Triangular.quotientMap k (A.diagonalAlg q) a) = 0
  exact ⟨fun h => by rw [h, map_zero], fun h => (eightCoordinates k).injective (by simpa using h)⟩

variable [Module.Finite k F] (E : Type*) [Field E] [Algebra k E]

noncomputable def scalarExtensionQuotientEquiv :
    (E ⊗[k] ConvertedAlgebra k q F ⧸ Ring.jacobson (E ⊗[k] ConvertedAlgebra k q F)) ≃ₐ[E]
      (Fin 8 → E) :=
  ArExplicit.scalarExtension_semisimpleQuotientEquiv E (diagonalAlg q F)
    (diagonalAlg_surjective q F) (radical_eq_ker_diagonal q F)

theorem scalarExtension_jacobson_fourth_ne_bot (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    (Ring.jacobson (E ⊗[k] ConvertedAlgebra k q F)) ^ 4 ≠ ⊥ :=
  scalarExtension_radical_pow_ne_bot E 4 (jacobson_fourth_ne_bot q F hq hq1)

end ArExplicit.ConvertedAlgebra

end OAI
