import OAI.Analysis.KadisonKastler.PublishedTwoRatioProduct
import OAI.Analysis.KadisonKastler.SpatialSiteBalance
import OAI.Analysis.KadisonKastler.TwoRatioProductType
import OAI.Analysis.KadisonKastler.SpatialProductSeparating
import OAI.Analysis.KadisonKastler.SpatialSeparability

namespace OAI

/-! # The fixed product makes a cyclically represented factor type III₁

The only product-construction input contains finite matrix moments and
the two site eigenoperators. The centralizer and core criteria then establish type III₁.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

private theorem product_matrix_entry_ne_zero {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Nontrivial K]
    (E : Generator.MatrixUnitSystem (Fin 2) (K →L[ℂ] K)) (i j : Fin 2) :
    E.entry i j ≠ 0 := by
  intro hz
  have hm := E.mul_entry i j j i
  rw [hz, zero_mul, ite_eq_left rfl] at hm
  exact E.diagonal_ne_zero i hm.symm

theorem TwoRatioProductModel.tensor_typeIII1
    (P : TwoRatioProductModel.{u})
    (hModular : PublishedModularSpectralResolution.{u})
    (hK : PublishedKaplanskyDensity.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (hClass : PublishedFactorialModularCore.{u})
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (hM : ScalarCenter M) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hc : DenseRange (algebraVectorMap M Ω))
    (hs : Function.Injective (algebraVectorMap M Ω)) :
    TypeIII1Factor (spatialProductAlgebra M P.stages.algebra) := by
  have : Nontrivial H := by
    refine ⟨⟨Ω, 0, ?_⟩⟩
    intro he
    have hn := hΩ
    rw [he, norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨dM, _⟩ := (hModular H M Ω hc hs).some
  obtain ⟨dD, _⟩ := (hModular P.K P.stages.algebra P.stages.vector
    P.stages.cyclic P.stages.separating).some
  have hpc := denseRange_spatialProduct_vector M P.stages.algebra Ω P.stages.vector
    hc P.stages.cyclic
  have hps := separating_spatialProduct_vector M P.stages.algebra Ω P.stages.vector
    hc P.stages.cyclic dM dD
  obtain ⟨_, mP⟩ := (hModular (SpatialHilbert H P.K) (spatialProductAlgebra M P.stages.algebra)
    (tensorVector P.stages.vector Ω) hpc hps).some
  let lambdaMatrix := P.coordinates.site (Sum.inl 0)
  let muMatrix := P.coordinates.site (Sum.inr 0)
  have hLambda := P.coordinates.twoRatio_site_algebra_le (Sum.inl 0) (lambdaMatrix.entry_mem 0 1)
  have hMu := P.coordinates.twoRatio_site_algebra_le (Sum.inr 0) (muMatrix.entry_mem 0 1)
  apply P.stages.tensor_typeIII1 hK hSpectral hDiagonal hClass M hM Ω hΩ hc hps mP
    (lambdaMatrix.entry 0 1) (muMatrix.entry 0 1) hLambda hMu
    (product_matrix_entry_ne_zero lambdaMatrix 0 1)
    (product_matrix_entry_ne_zero muMatrix 0 1)
  · intro t
    exact PointedMatrixSites.twoRatio_site_spatial_modular_star_eigen hK M P.stages Ω
      P.coordinates hps mP (Sum.inl 0) t
  · intro t
    exact PointedMatrixSites.twoRatio_site_spatial_modular_star_eigen hK M P.stages Ω
      P.coordinates hps mP (Sum.inr 0) t

end

end KadisonKastler

end OAI
