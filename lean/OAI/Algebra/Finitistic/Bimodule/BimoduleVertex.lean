import OAI.Algebra.Finitistic.Rectification.VertexFunctor
import OAI.Algebra.Finitistic.Rectification.CornerTensor
import OAI.Algebra.Finitistic.Rectification.ColumnComplex

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BimoduleVertex

section
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

abbrev restriction : Bᵐᵒᵖ →+* B ⊗[k] Bᵐᵒᵖ :=
  Algebra.TensorProduct.includeRight.toRingHom
abbrev vertex (e : B) : B ⊗[k] Bᵐᵒᵖ := e ⊗ₜ[k] 1

theorem vertex_idempotent (e : B) (he : e*e=e) :
    vertex k B e * vertex k B e = vertex k B e := by
  simp [vertex,Algebra.TensorProduct.tmul_mul_tmul,he]

theorem vertex_commute (e : B) (b : Bᵐᵒᵖ) :
    vertex k B e * restriction k B b = restriction k B b * vertex k B e := by
  simp [vertex,restriction,Algebra.TensorProduct.tmul_mul_tmul]

/-- The original left vertex action, with the right B-module structure retained. -/
abbrev functor (e : B) : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ) ⥤ ModuleCat.{u} Bᵐᵒᵖ :=
  VertexFunctor.functor (restriction k B) (vertex k B e) (vertex_commute k B e)

theorem map_shortExact (e : B) (he : e*e=e)
    (S : ShortComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))) (hS : S.ShortExact) :
    (S.map (functor k B e)).ShortExact :=
  VertexFunctor.map_shortExact _ _ (vertex_idempotent k B e he) _ S hS

end
universe u
variable {k : Type u} [Field k]
variable {V W U : Type u} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
local notation "T" => ThreeVertexAlgebra μ
variable (N : ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ)
attribute [local instance] ExternalTensor.Section4.rightModuleK
  ExternalTensor.rightModule ExternalTensor.bimodule

abbrev columnObj (j : Fin 3) : ModuleCat.{u} (T ⊗[k] Tᵐᵒᵖ) :=
  ModuleCat.of _ (ExternalTensor.Column k T N (ThreeVertexAlgebra.vertex μ j))
abbrev columnFixed (i j : Fin 3) :=
  VertexFunctor.fixed (restriction k T) (vertex k T (ThreeVertexAlgebra.vertex μ i))
    (vertex_commute k T (ThreeVertexAlgebra.vertex μ i)) (columnObj μ N j)

/-- Identifies the original enveloping vertex action with its corner projector. -/
def columnFixedEquiv (i j : Fin 3) :
    columnFixed μ N i j ≃ₗ[Tᵐᵒᵖ]
    TensorProjection.fixed (B := T) (N := N) (CornerProjection.projection μ i j) := by
  refine
    { toFun := fun x => ⟨x.val, ?_⟩
      invFun := fun x => ⟨x.val, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun b x => ?_ }
  · apply (CornerTensor.fixed_iff_left_action μ N i j _).2
    have hx := (VertexFunctor.mem_fixed _ _ _ _ x.val).1 x.property
    change (ThreeVertexAlgebra.vertex μ i ⊗ₜ[k] (1 : Tᵐᵒᵖ)) • x.val = x.val at hx
    exact (ExternalTensor.left_eq_enveloping k T
      (ExternalTensor.leftIdeal T (ThreeVertexAlgebra.vertex μ j)) N
      (ThreeVertexAlgebra.vertex μ i) x.val).trans hx
  · apply Subtype.ext
    exact (ExternalTensor.right_eq_enveloping k T
      (ExternalTensor.leftIdeal T (ThreeVertexAlgebra.vertex μ j)) N b x.val).symm

  · apply (VertexFunctor.mem_fixed _ _ _ _ _).2
    have hx := (CornerTensor.fixed_iff_left_action μ N i j x.val).1 x.property
    exact (ExternalTensor.left_eq_enveloping k T
      (ExternalTensor.leftIdeal T (ThreeVertexAlgebra.vertex μ j)) N
      (ThreeVertexAlgebra.vertex μ i) x.val).symm.trans hx
/-- A column's own vertex is its original right module, with no replacement action. -/
def diagonalEquiv (i : Fin 3) :
    (functor k T (ThreeVertexAlgebra.vertex μ i)).obj
      ((ExternalTensor.Section4.columnFunctor k T
        (ThreeVertexAlgebra.vertex μ i)).obj N) ≃ₗ[Tᵐᵒᵖ] N :=
  (columnFixedEquiv μ N i i).trans (CornerTensor.diagonalColumnEquiv μ N i)
end LittleFinitistic.BimoduleVertex

end

end OAI
