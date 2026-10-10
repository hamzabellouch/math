import OAI.Analysis.KadisonKastler.SpatialReducingProjection
import OAI.Analysis.KadisonKastler.IsometricRestriction

namespace OAI

/-! # Tensoring the constructed faithful cyclic representation

The tensor representation is a restriction of countable amplification.
Its defining isometry and its bounded weak continuity are concrete.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Generator.Tracial Filter
open scoped TensorProduct Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def faithfulTensorEmbedding (M : VonNeumannAlgebra H) :
    SpatialHilbert (faithfulCyclicSpace M) K →ₗᵢ[ℂ]
      CountableHilbertSum (SpatialHilbert H K) :=
  (countableTensorEquiv (H := H) (K := K)).toLinearIsometry.comp
    (spatialSubspaceInclusion (K := K) (faithfulCyclicSpace M))

omit [Nontrivial H] [CompleteSpace K] in
@[simp] theorem faithfulTensorEmbedding_tmul (M : VonNeumannAlgebra H)
    (x : faithfulCyclicSpace M) (y : K) :
    faithfulTensorEmbedding M
      ((x ⊗ₜ[ℂ] y : faithfulCyclicSpace M ⊗[ℂ] K) :
        SpatialHilbert (faithfulCyclicSpace M) K) = countableTensorVector x.val y := by
  change countableTensorEquiv (spatialIsometry (faithfulCyclicSpace M).subtypeₗᵢ
    (LinearIsometry.id : K →ₗᵢ[ℂ] K) _) = _
  rw [spatialIsometry_tmul]
  exact countableTensorEquiv_tmul x.val y

omit [Nontrivial H] in
theorem faithfulTensorEmbedding_projection (M : VonNeumannAlgebra H) :
    (faithfulTensorEmbedding (K := K) M).toContinuousLinearMap.comp
      (faithfulTensorEmbedding (K := K) M).toContinuousLinearMap.adjoint =
      (countableTensorEquiv (H := H) (K := K)).conjStarAlgEquiv
        (spatialLeft (faithfulCyclicSpace M).starProjection) := by
  exact (isometry_equiv_comp_projection (countableTensorEquiv (H := H) (K := K))
    (spatialSubspaceInclusion (K := K) (faithfulCyclicSpace M))).trans
      (congrArg (countableTensorEquiv (H := H) (K := K)).conjStarAlgEquiv
        (spatialSubspaceInclusion_projection (K := K) (faithfulCyclicSpace M)))

def faithfulTensorHom (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    Algebra (spatialProductAlgebra M D) →⋆ₐ[ℂ]
      (SpatialHilbert (faithfulCyclicSpace M) K →L[ℂ] SpatialHilbert (faithfulCyclicSpace M) K) :=
  isometricRestriction (faithfulTensorEmbedding M)
    (l2DiagonalHom.comp (spatialProductAlgebra M D).toStarSubalgebra.subtype)
    (fun a => by
      rw [faithfulTensorEmbedding_projection]
      exact faithfulCyclic_tensor_projection_commutes M D a.val a.property)

omit [Nontrivial H] in
@[simp] theorem faithfulTensorHom_intertwines (M : VonNeumannAlgebra H)
    (D : VonNeumannAlgebra K) (a : Algebra (spatialProductAlgebra M D))
    (z : SpatialHilbert (faithfulCyclicSpace M) K) :
    faithfulTensorEmbedding M (faithfulTensorHom M D a z) =
      l2Diagonal a.val (faithfulTensorEmbedding M z) :=
  isometricRestriction_apply _ _ _ a z

omit [Nontrivial H] in
theorem faithfulTensorHom_left (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (a : Algebra M) :
    faithfulTensorHom M D ⟨spatialLeft a.val, spatialLeft_mem_product M D a.property⟩ =
      spatialLeft (K := K) (faithfulCyclicHom M a) := by
  apply spatialLinearMap_ext
  intro x y
  apply (faithfulTensorEmbedding M).injective
  refine (faithfulTensorHom_intertwines M D _ _).trans ?_
  rw [faithfulTensorEmbedding_tmul]
  have hl : l2Diagonal (spatialLeft (K := K) a.val) (countableTensorVector x.val y) =
      countableTensorVector (l2Diagonal a.val x.val) y := by
    ext n
    exact (spatialTensorOp_coe a.val (1 : K →L[ℂ] K) (x.val n ⊗ₜ[ℂ] y)).trans
      (by simp only [TensorProduct.mapL_tmul, one_apply_eq_self]; rfl)
  have hr : spatialLeft (K := K) (faithfulCyclicHom M a)
      ((x ⊗ₜ[ℂ] y : faithfulCyclicSpace M ⊗[ℂ] K) :
        SpatialHilbert (faithfulCyclicSpace M) K) =
      (((faithfulCyclicHom M a x) ⊗ₜ[ℂ] y : faithfulCyclicSpace M ⊗[ℂ] K) :
        SpatialHilbert (faithfulCyclicSpace M) K) := by
    exact (spatialTensorOp_coe (faithfulCyclicHom M a) (1 : K →L[ℂ] K)
      (x ⊗ₜ[ℂ] y)).trans (by simp only [TensorProduct.mapL_tmul, one_apply_eq_self])
  exact hl.trans ((congrArg (fun z => countableTensorVector z y)
    (faithfulCyclicHom_apply M a x).symm).trans
      ((faithfulTensorEmbedding_tmul M (faithfulCyclicHom M a x) y).symm.trans
        (congrArg (faithfulTensorEmbedding (K := K) M) hr.symm)))

omit [Nontrivial H] in
theorem faithfulTensorHom_right (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (b : Algebra D) :
    faithfulTensorHom M D ⟨spatialRight b.val, spatialRight_mem_product M D b.property⟩ =
      spatialRight (H := faithfulCyclicSpace M) b.val := by
  apply spatialLinearMap_ext
  intro x y
  apply (faithfulTensorEmbedding M).injective
  refine (faithfulTensorHom_intertwines M D _ _).trans ?_
  rw [faithfulTensorEmbedding_tmul]
  have hl : l2Diagonal (spatialRight (H := H) b.val) (countableTensorVector x.val y) =
      countableTensorVector x.val (b.val y) := by
    ext n
    exact (spatialTensorOp_coe (1 : H →L[ℂ] H) b.val (x.val n ⊗ₜ[ℂ] y)).trans
      (by simp only [TensorProduct.mapL_tmul, one_apply_eq_self]; rfl)
  have hr : spatialRight (H := faithfulCyclicSpace M) b.val
      ((x ⊗ₜ[ℂ] y : faithfulCyclicSpace M ⊗[ℂ] K) :
        SpatialHilbert (faithfulCyclicSpace M) K) =
      ((x ⊗ₜ[ℂ] b.val y : faithfulCyclicSpace M ⊗[ℂ] K) :
        SpatialHilbert (faithfulCyclicSpace M) K) := by
    exact (spatialTensorOp_coe (1 : faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M)
      b.val (x ⊗ₜ[ℂ] y)).trans (by simp only [TensorProduct.mapL_tmul, one_apply_eq_self])
  exact hl.trans ((faithfulTensorEmbedding_tmul M x (b.val y)).symm.trans
    (congrArg (faithfulTensorEmbedding (K := K) M) hr.symm))

omit [Nontrivial H] in
theorem faithfulTensorHom_tendsto_weak (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    {ι : Type*} {l : Filter ι} (a : ι → Algebra (spatialProductAlgebra M D))
    (b : Algebra (spatialProductAlgebra M D)) (C : ℝ) (hn : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hweak : ∀ x y : SpatialHilbert H K,
      Tendsto (fun i => inner ℂ y ((a i).val x)) l (𝓝 (inner ℂ y (b.val x))))
    (x y : SpatialHilbert (faithfulCyclicSpace M) K) :
    Tendsto (fun i => inner ℂ y (faithfulTensorHom M D (a i) x)) l
      (𝓝 (inner ℂ y (faithfulTensorHom M D b x))) := by
  change Tendsto (fun i => inner ℂ y
    ((faithfulTensorEmbedding M).toContinuousLinearMap.adjoint
      (l2Diagonal (a i).val (faithfulTensorEmbedding M x)))) l
    (𝓝 (inner ℂ y ((faithfulTensorEmbedding M).toContinuousLinearMap.adjoint
      (l2Diagonal b.val (faithfulTensorEmbedding M x)))))
  simp only [ContinuousLinearMap.adjoint_inner_right]
  exact l2Diagonal_tendsto_weak (fun i => (a i).val) b.val C hn hweak _ _

end

end KadisonKastler

end OAI
