import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorBimoduleComparison

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
namespace VertexTensor

attribute [local instance] termScalar termTower

/-- The actual arrow between BC vertex projectives. -/
def arrowMap (i : Fin l) :
    IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i.castSucc)) →ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ]
    IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i.succ)) where
  toFun x := ⟨((1:B) ⊗ₜ[k] ChainAlgebra.arrow k l i) * x.val, by
    change ((1:B) ⊗ₜ[k] ChainAlgebra.vertex k l i.succ) *
      (((1:B) ⊗ₜ[k] ChainAlgebra.arrow k l i) * x.val) = _
    rw [← mul_assoc,Algebra.TensorProduct.tmul_mul_tmul,one_mul,ChainAlgebra.vertex_target_arrow]⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' r x := Subtype.ext (mul_assoc _ _ r.unop).symm

/-- Tensor the actual arrow with O; no differential is assumed. -/
def rawDifferential (i : Fin l) : VertexTensor P a l i.castSucc →ₗ[k] VertexTensor P a l i.succ :=
  BalancedTensor.mapLeft (BimoduleO P a l) (arrowMap (k := k) (B := B) l i)

theorem arrow_coordinate (i : Fin l) (v : BimoduleO P a l) :
    (ChainAlgebra.arrow k l i • v : BimoduleO P a l) i.succ =
      (P.d (a+(i.castSucc.val:ℤ)) (a+(i.succ.val:ℤ))).hom (v i.castSucc) := by
  have h := OrdinaryTerms.action_arrow
    (intervalTerms (underlyingComplex (k := k) P) a l)
    (intervalDifferential (underlyingComplex (k := k) P) a l) i v
  have h' := congrArg (fun w => w i.succ) h
  change OrdinaryTerms.action (intervalTerms (underlyingComplex (k := k) P) a l)
    (intervalDifferential (underlyingComplex (k := k) P) a l) (ChainAlgebra.arrow k l i) v i.succ =
      intervalDifferential (underlyingComplex (k := k) P) a l i.castSucc i.succ (v i.castSucc)
  simpa only [Pi.single_eq_same] using h' 

/-- Evaluation identifies the computed arrow differential with the genuine d_P. -/
theorem evaluation_differential (i : Fin l) (z : VertexTensor P a l i.castSucc) :
    evaluation P a l i.succ (rawDifferential P a l i z) =
      (P.d (a+(i.castSucc.val:ℤ)) (a+(i.succ.val:ℤ))).hom (evaluation P a l i.castSucc z) := by
  have h : (evaluation P a l i.succ).toLinearMap.comp (rawDifferential P a l i) =
      ((P.d (a+(i.castSucc.val:ℤ)) (a+(i.succ.val:ℤ))).hom.restrictScalars k).comp
        (evaluation P a l i.castSucc).toLinearMap := by
    apply BalancedTensor.ext
    intro m v
    change ((((1:B) ⊗ₜ[k] ChainAlgebra.arrow k l i) * m.val) • v : BimoduleO P a l) i.succ =
      (P.d (a+(i.castSucc.val:ℤ)) (a+(i.succ.val:ℤ))).hom ((m.val • v : BimoduleO P a l) i.castSucc)
    have h : (((1:B) ⊗ₜ[k] ChainAlgebra.arrow k l i) * m.val) • v =
        ChainAlgebra.arrow k l i • (m.val • v) := by
      rw [mul_smul, BimoduleO.tensor_smul, one_smul]
    exact (congrArg (fun w : BimoduleO P a l => w i.succ) h).trans
      (arrow_coordinate P a l i (m.val • v))
  exact congrArg (fun f => f z) h

/-- The actual tensor differential retains both B-actions. -/
def differential (i : Fin l) : VertexTensor P a l i.castSucc →ₗ[Enveloping k B] VertexTensor P a l i.succ where
  __ := (rawDifferential P a l i).toAddHom
  map_smul' r z := by
    apply (evaluation P a l i.succ).injective
    change evaluation P a l i.succ (rawDifferential P a l i (r • z)) =
      evaluation P a l i.succ (r • rawDifferential P a l i z)
    rw [evaluation_differential, evaluation_smul, evaluation_smul, evaluation_differential]
    exact (P.d _ _).hom.map_smul r _

/-- Equality of bimodule maps, with the source's actual differential. -/
theorem bimodule_differential_comparison (i : Fin l) :
    (bimoduleEquiv P a l i.succ).toLinearMap.comp (differential P a l i) =
      (P.d (a+(i.castSucc.val:ℤ)) (a+(i.succ.val:ℤ))).hom.comp
        (bimoduleEquiv P a l i.castSucc).toLinearMap := by
  ext z
  exact evaluation_differential P a l i z
end VertexTensor
end LittleFinitistic.OrdinarySimulation

end

end OAI
