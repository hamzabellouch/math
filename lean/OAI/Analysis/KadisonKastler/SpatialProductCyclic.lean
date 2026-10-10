import OAI.Analysis.KadisonKastler.SpatialSliceRecovery
import OAI.Analysis.KadisonKastler.ProductMatrixStages

namespace OAI

/-! # Cyclic product vectors in the actual spatial tensor product -/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem ProductMatrixStages.cyclic (P : ProductMatrixStages (H := K)) :
    DenseRange (algebraVectorMap P.algebra P.vector) := by
  apply Dense.mono _ P.local_cyclic
  rintro _ ⟨⟨n, a⟩, rfl⟩
  exact ⟨⟨a, P.local_le n a.property⟩, rfl⟩

/-- Dense orbits in each tensor leg give a dense orbit for the product
vector. The proof takes place in the completed Hilbert tensor product. -/
theorem denseRange_spatialProduct_vector
    (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) (Ω : H) (ξ : K)
    (hM : DenseRange (algebraVectorMap M Ω))
    (hD : DenseRange (algebraVectorMap D ξ)) :
    DenseRange (algebraVectorMap (spatialProductAlgebra M D) (tensorVector ξ Ω)) := by
  let V := algebraVectorMap (spatialProductAlgebra M D) (tensorVector ξ Ω)
  change Dense (LinearMap.range V : Set (SpatialHilbert H K))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply bot_unique
  intro v hv
  change v = 0
  apply spatialTensor_vector_ext
  intro x η
  rw [inner_zero_right]
  have hfinite (a : Algebra M) (b : Algebra D) :
      inner ℂ (tensorVector (b.val ξ) (a.val Ω)) v = 0 := by
    have hab : spatialTensorOp a.val b.val ∈ spatialProductAlgebra M D := by
      have hh := (spatialProductAlgebra M D).mul_mem
        (spatialLeft_mem_product M D a.property) (spatialRight_mem_product M D b.property)
      have he : spatialTensorOp a.val b.val = spatialLeft (K := K) a.val *
          spatialRight (H := H) b.val := by
        change spatialTensorOp a.val b.val = spatialTensorOp a.val 1 * spatialTensorOp 1 b.val
        rw [← spatialTensorOp_mul, mul_one, one_mul]
      rwa [he]
    have he := hv (V ⟨spatialTensorOp a.val b.val, hab⟩) ⟨_, rfl⟩
    simpa only [V, algebraVectorMap, LinearMap.coe_mk, AddHom.coe_mk,
      tensorVector_apply, spatialTensorOp_coe, TensorProduct.mapL_tmul] using he
  have hsecond (a : Algebra M) : inner ℂ (tensorVector η (a.val Ω)) v = 0 := by
    refine hD.induction_on (p := fun z => inner ℂ (tensorVector z (a.val Ω)) v = 0) η ?_ ?_
    · change IsClosed {z : K | inner ℂ (leftTensorVector (a.val Ω) z) v = 0}
      exact isClosed_eq (by fun_prop) continuous_const
    · exact hfinite a
  change inner ℂ (tensorVector η x) v = 0
  refine hM.induction_on (p := fun z => inner ℂ (tensorVector η z) v = 0) x ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact hsecond

end

end KadisonKastler

end OAI
