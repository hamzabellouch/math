import OAI.Algebra.AuslanderReiten.Algebras.TensorStructure
import OAI.Algebra.AuslanderReiten.Triangular.TriangularRadical
import OAI.Algebra.AuslanderReiten.Homology.SplitQuotient

namespace OAI

namespace ArExplicit

abbrev ConvertedAlgebra (k : Type*) [Field k] (q : k) (F : Type*) := Triangular (A k q) F

namespace ConvertedAlgebra

variable {k : Type*} [Field k] (q : k) (F : Type*) [AddCommGroup F]
variable [Module (A k q) F] [Module (A k q)ᵐᵒᵖ F]
variable [SMulCommClass (A k q) (A k q)ᵐᵒᵖ F]

def radicalU : ConvertedAlgebra k q F := ⟨A.radicalU q, 0, 0⟩

def radicalT : ConvertedAlgebra k q F := ⟨A.radicalT q, 0, 0⟩

theorem radicalU_mem : radicalU q F ∈ Ring.jacobson (ConvertedAlgebra k q F) := by
  apply Triangular.mem_jacobson_iff _ |>.mpr
  exact ⟨A.radicalU_mem q, Submodule.zero_mem _⟩

theorem radicalT_mem : radicalT q F ∈ Ring.jacobson (ConvertedAlgebra k q F) := by
  apply Triangular.mem_jacobson_iff _ |>.mpr
  exact ⟨A.radicalT_mem q, Submodule.zero_mem _⟩

theorem jacobson_fourth_ne_bot (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    (Ring.jacobson (ConvertedAlgebra k q F)) ^ 4 ≠ ⊥ := by
  have h4 := Ideal.mul_mem_mul
    (Ideal.mul_mem_mul (Ideal.mul_mem_mul (radicalU_mem q F) (radicalT_mem q F))
      (radicalU_mem q F)) (radicalT_mem q F)
  have hmem : ((radicalU q F * radicalT q F) * radicalU q F) * radicalT q F ∈
      (Ring.jacobson (ConvertedAlgebra k q F)) ^ 4 := by
    simpa only [Submodule.pow_succ, Submodule.pow_zero, Submodule.one_mul] using h4
  intro h
  rw [h] at hmem
  have ht := congrArg Triangular.top (show _ = 0 from hmem)
  exact A.fourfold_product_ne_zero q hq hq1 ht

variable [Module k F]
variable [IsScalarTower k (A k q) F] [IsScalarTower k (A k q)ᵐᵒᵖ F]
variable [SMulCommClass k (A k q) F] [SMulCommClass k (A k q)ᵐᵒᵖ F]

noncomputable def semisimpleQuotientEquiv :
    (ConvertedAlgebra k q F ⧸ Ring.jacobson (ConvertedAlgebra k q F)) ≃ₐ[k] (Fin 8 → k) :=
  (Triangular.semisimpleQuotientEquiv (F := F) k (A.diagonalAlg q)
    (A.diagonalAlg_surjective q) (A.radical_eq_ker_diagonal q)).trans (eightCoordinates k)

end ConvertedAlgebra
end ArExplicit

end OAI
