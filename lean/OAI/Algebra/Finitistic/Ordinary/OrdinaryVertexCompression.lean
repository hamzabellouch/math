import OAI.Algebra.Finitistic.Ordinary.OrdinaryCompression
import OAI.Algebra.Finitistic.Tensor.IdempotentTensor

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation.Compression
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) (l : ℕ)

/-- Coordinate insertion is linear over the full coefficient algebra A. -/
def insert (i : Fin (l+1)) : P.X (a+(i.val:ℤ)) →ₗ[A] Compression P a l :=
  LinearMap.single A (fun i : Fin (l+1) => P.X (a+(i.val:ℤ))) i

def project (i : Fin (l+1)) : Compression P a l →ₗ[A] P.X (a+(i.val:ℤ)) := LinearMap.proj i

theorem vertex_action (i : Fin (l+1)) (v : Compression P a l) :
    ChainAlgebra.vertex k l i • v = insert P a l i (project P a l i v) := by
  exact OrdinaryTerms.action_vertex (intervalTerms (underlyingComplex (k := k) P) a l)
    (intervalDifferential (underlyingComplex (k := k) P) a l) i v

/-- The vertex part is a submodule over A, hence retains both B-actions when A=B tensor B-op. -/
def vertexSpace (i : Fin (l+1)) : Submodule A (Compression P a l) where
  carrier := {v | ChainAlgebra.vertex k l i • v = v}
  zero_mem' := smul_zero _
  add_mem' := by
    intro x y hx hy
    change ChainAlgebra.vertex k l i • (x+y) = x+y
    rw [smul_add, hx, hy]
  smul_mem' r v hv := by
    change ChainAlgebra.vertex k l i • (r • v) = r • v
    rw [smul_comm, hv]

def vertexInsert (i : Fin (l+1)) : P.X (a+(i.val:ℤ)) →ₗ[A] vertexSpace (k := k) P a l i :=
  (insert P a l i).codRestrict _ (fun v => by
    change ChainAlgebra.vertex k l i • insert P a l i v = insert P a l i v
    rw [vertex_action]
    congr 1
    change (Pi.single i v : ∀ j : Fin (l+1), P.X (a+(j.val:ℤ))) i = v
    simp)

/-- Actual A-linear identification of the compressed vertex with its original term. -/
def vertexEquiv (i : Fin (l+1)) : vertexSpace (k := k) P a l i ≃ₗ[A] P.X (a+(i.val:ℤ)) where
  __ := (project P a l i).comp (vertexSpace (k := k) P a l i).subtype
  invFun := vertexInsert (k := k) P a l i
  left_inv x := by
    apply Subtype.ext
    exact (vertex_action (k := k) P a l i x.val).symm.trans x.property
  right_inv v := by
    change (Pi.single i v : ∀ j : Fin (l+1), P.X (a+(j.val:ℤ))) i = v
    simp

/-- Change only the scalar description of the same actual vertex subspace. -/
def vertexSpaceScalarEquiv (i : Fin (l+1)) :
    IdempotentTensor.leftSpace (k := k) (ChainAlgebra.vertex k l i) (Compression P a l) ≃ₗ[k]
      vertexSpace (k := k) P a l i where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The genuine balanced tensor on a vertex projective evaluates to the original term. -/
def vertexTensorEquiv (i : Fin (l+1)) :
    BalancedTensor.Tensor k (ChainAlgebra k l)
      (IdempotentTensor.rightIdeal (ChainAlgebra.vertex k l i)) (Compression P a l) ≃ₗ[k]
      (underlyingComplex (k := k) P).X (a+(i.val:ℤ)) := by
  letI (n : ℤ) : Module k (P.X n) := Module.compHom _ (algebraMap k A)
  letI (n : ℤ) : IsScalarTower k A (P.X n) := IsScalarTower.of_compHom k A (P.X n)
  exact (IdempotentTensor.tensorEquiv (k := k) (ChainAlgebra.vertex k l i) (Compression P a l)
    (ChainAlgebra.vertex_idempotent k l i)).trans
      ((vertexSpaceScalarEquiv (k := k) P a l i).trans
        ((vertexEquiv (k := k) P a l i).restrictScalars k))
end LittleFinitistic.OrdinarySimulation.Compression

end

end OAI
