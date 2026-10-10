import OAI.Algebra.Finitistic.Rectification.VertexDecomposition
import Mathlib.LinearAlgebra.Pi

namespace OAI
noncomputable section
namespace LittleFinitistic.VertexModuleAssembly
open VertexDecomposition
universe u v w
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}
variable (D : DirectedBound.DirectedSystem k A n)
variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module A N]
  [IsScalarTower k A M] [IsScalarTower k A N]
variable (E : ∀ i, Space D M i ≃ₗ[k] Space D N i)

/-- Assemble specified vertex isomorphisms into a vector-space isomorphism. -/
def assembled : M ≃ₗ[k] N :=
  (equiv D M).trans ((LinearEquiv.piCongrRight E).trans (equiv D N).symm)

lemma project_assembled (i : Fin n) (x : M) :
    project D N i (assembled D E x) = E i (project D M i x) := by
  exact congrFun ((equiv D N).apply_symm_apply
    ((LinearEquiv.piCongrRight E) (equiv D M x))) i

lemma assembled_vertex (i : Fin n) (x : Space D M i) :
    assembled D E x.val = (E i x).val := by
  apply (equiv D N).injective
  funext j
  rw [equiv_apply, project_assembled, equiv_apply]
  by_cases h : j = i
  · subst j
    rw [project_self, project_self]
  · rw [project_other D M j i h, project_other D N j i h, map_zero]

/-- The assembled map commutes with every vertex idempotent. -/
theorem vertex_smul (i : Fin n) (x : M) :
    assembled D E (D.e i • x) = D.e i • assembled D E x := by
  have h := assembled_vertex D E i (project D M i x)
  have hp := congrArg Subtype.val (project_assembled D E i x)
  exact h.trans hp.symm

/-- A supported arrow acts between its actual source and target subspaces. -/
def arrow {i j : Fin n} (a : A) (ha : D.e j * a = a) :
    Space D M i →ₗ[k] Space D M j where
  toFun x := ⟨a • x.val, by
    change D.e j • (a • x.val) = a • x.val
    rw [← mul_smul, ha]⟩
  map_add' x y := Subtype.ext (smul_add _ _ _)
  map_smul' c x := Subtype.ext (smul_comm _ _ _)

/-- Vertexwise compatibility with an actual arrow gives compatibility of the
assembled map on every element of the full module. -/
theorem arrow_smul {i j : Fin n} (a : A) (hl : D.e j * a = a) (hr : a * D.e i = a)
    (hE : ∀ x : Space D M i, E j (arrow D a hl x) = arrow D a hl (E i x))
    (x : M) : assembled D E (a • x) = a • assembled D E x := by
  have hax : a • (project D M i x).val = a • x := by
    change a • (D.e i • x) = a • x
    rw [← mul_smul, hr]
  have h := assembled_vertex D E j (arrow D a hl (project D M i x))
  change assembled D E (a • (project D M i x).val) =
    (E j (arrow D a hl (project D M i x))).val at h
  rw [hax, hE] at h
  have hp := congrArg Subtype.val (project_assembled D E i x)
  change D.e i • assembled D E x = (E i (project D M i x)).val at hp
  change assembled D E (a • x) = a • (E i (project D M i x)).val at h
  rw [← hp, ← mul_smul, hr] at h
  exact h
end LittleFinitistic.VertexModuleAssembly

end

end OAI
