import OAI.Analysis.KadisonKastler.ProductMatrixStages
import OAI.Analysis.KadisonKastler.SpatialMatrixDensity

namespace OAI

/-! # Product vector states and centralization on the second tensor leg

Finite spatial matrix images give the product-state identity on a dense
star algebra. The actual strong-density theorem extends centralization
to the spatial von Neumann product.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator
open scoped TensorProduct BigOperators

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
theorem productVectorState_spatialTensor (Ω : H) (ξ : K)
    (a : H →L[ℂ] H) (b : K →L[ℂ] K) :
    productVectorState (tensorVector ξ Ω) (spatialTensorOp a b) =
      productVectorState Ω a * productVectorState ξ b := by
  simp only [productVectorState, tensorVector_apply, spatialTensorOp_coe,
    TensorProduct.mapL_tmul, UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]

theorem spatialRight_centralizes_simple_tensor
    (D : VonNeumannAlgebra K) (Ω : H) (ξ : K) (u : K →L[ℂ] K)
    (hc : ProductStateCentralizes D ξ u)
    (a : H →L[ℂ] H) (b : K →L[ℂ] K) (hb : b ∈ D) :
    productVectorState (tensorVector ξ Ω) (spatialRight u * spatialTensorOp a b) =
      productVectorState (tensorVector ξ Ω) (spatialTensorOp a b * spatialRight u) := by
  change productVectorState (tensorVector ξ Ω) (spatialTensorOp 1 u * spatialTensorOp a b) =
    productVectorState (tensorVector ξ Ω) (spatialTensorOp a b * spatialTensorOp 1 u)
  rw [← spatialTensorOp_mul, ← spatialTensorOp_mul, one_mul, mul_one,
    productVectorState_spatialTensor, productVectorState_spatialTensor, hc b hb]

/-- The second-leg state centralizer remains in the centralizer of a
product vector state, for the actual spatial von Neumann product. -/
theorem spatialRight_productStateCentralizes
    (hK : PublishedKaplanskyDensity.{u}) (M : VonNeumannAlgebra H)
    (P : ProductMatrixStages (H := K)) (Ω : H) (u : K →L[ℂ] K)
    (hc : ProductStateCentralizes P.algebra P.vector u) :
    ProductStateCentralizes (spatialProductAlgebra M P.algebra)
      (tensorVector P.vector Ω) (spatialRight (H := H) u) := by
  rw [show P.algebra = generatedVonNeumannAlgebra (⨆ n, (P.matrix n).algebra) from rfl,
    ← generated_spatialMatrixAlgebra_eq_product M P.matrix hK P.increasing]
  apply productStateCentralizes_of_local (fun n => spatialMatrixAlgebra M (P.matrix n))
    (fun i j hij => spatialMatrixAlgebra_mono M _ _ (P.increasing hij))
  intro n x hx
  obtain ⟨X, rfl⟩ := hx
  change productVectorLinear (tensorVector P.vector Ω)
      (spatialRight u * spatialMatrixAlgebraHom M (P.matrix n) X) =
    productVectorLinear (tensorVector P.vector Ω)
      (spatialMatrixAlgebraHom M (P.matrix n) X * spatialRight u)
  rw [spatialMatrixAlgebraHom_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact spatialRight_centralizes_simple_tensor P.algebra Ω P.vector u hc (X i j).val
    ((P.matrix n).entry i j) (P.local_le n ((P.matrix n).entry_mem i j))

end

end KadisonKastler

end OAI
