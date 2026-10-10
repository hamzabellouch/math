import OAI.Analysis.KadisonKastler.SpatialProductState
import OAI.Analysis.KadisonKastler.SpatialProductCyclic
import OAI.Analysis.KadisonKastler.TwoFrequencyCoreFactor
import OAI.Analysis.KadisonKastler.PublishedModularSpectral
import OAI.Analysis.KadisonKastler.PublishedModularCoreType
import OAI.Analysis.KadisonKastler.TwoRatioParameters

namespace OAI

/-! # The type III₁ conclusion for the fixed two-ratio product

The local finite-product data supply centralizer irreducibility. The two
site eigenoperators then force the regular core to be a factor, before
the published core-classification theorem is applied.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace H]
  [Nontrivial (SpatialHilbert H K)] [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]

/-- All factorial-core conclusions are derived from finite product data
and the two explicit site eigenoperators. The given modular resolution
is certified by its bounded KMS strip condition. -/
theorem ProductMatrixStages.tensor_typeIII1
    (P : ProductMatrixStages (H := K))
    (hK : PublishedKaplanskyDensity.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (hClass : PublishedFactorialModularCore.{u})
    (M : VonNeumannAlgebra H) (hM : ScalarCenter M) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hcyclic : DenseRange (algebraVectorMap M Ω))
    (hseparating : Function.Injective (algebraVectorMap (spatialProductAlgebra M P.algebra)
      (tensorVector P.vector Ω)))
    (m : ModularSpectralResolution (spatialProductAlgebra M P.algebra) (tensorVector P.vector Ω))
    (b₁ b₂ : K →L[ℂ] K) (hb₁ : b₁ ∈ P.algebra) (hb₂ : b₂ ∈ P.algebra)
    (hn₁ : b₁ ≠ 0) (hn₂ : b₂ ≠ 0)
    (heigen₁ : ∀ t : ℝ,
      unitaryConj (star (m.group (Multiplicative.ofAdd t))) (spatialRight (H := H) b₁) =
        regularCharacterScalar (Real.log fixedProductLambda) t • spatialRight (H := H) b₁)
    (heigen₂ : ∀ t : ℝ,
      unitaryConj (star (m.group (Multiplicative.ofAdd t))) (spatialRight (H := H) b₂) =
        regularCharacterScalar (Real.log fixedProductMu) t • spatialRight (H := H) b₂) :
    TypeIII1Factor (spatialProductAlgebra M P.algebra) := by
  have hnormalizes : ∀ t x, x ∈ spatialProductAlgebra M P.algebra →
      unitaryConj (m.group t) x ∈ spatialProductAlgebra M P.algebra := by
    intro t x hx
    change unitaryConj (m.group t) x ∈
      (spatialProductAlgebra M P.algebra : Set (SpatialHilbert H K →L[ℂ] SpatialHilbert H K))
    rw [← m.normalizes t]
    exact Set.mem_image_of_mem _ hx
  have hfixed : ∀ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ P.algebra →
      ProductStateCentralizes P.algebra P.vector u → ∀ t,
      unitaryConj (m.group t) (spatialRight (H := H) (u : K →L[ℂ] K)) =
        spatialRight (H := H) (u : K →L[ℂ] K) := by
    intro u hu hc
    exact m.centralizer_fixed _ (spatialRight_mem_product M P.algebra hu)
      (spatialRight_productStateCentralizes hK M P Ω u hc)
  have hfreq (r : ℝ) : 2 * Real.pi * (r / (2 * Real.pi)) = r := by
    have hp : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    field_simp
  have hcore := scalarCenter_regularCore_of_two_site_frequencies hSpectral hDiagonal
    M hM P.algebra P.vector P.unit_vector P.localSwaps P.separating
    m.group m.continuous hnormalizes hfixed b₁ b₂ hb₁ hb₂ hn₁ hn₂
    (Real.log fixedProductLambda / (2 * Real.pi))
    (Real.log fixedProductMu / (2 * Real.pi)) fixedProduct_frequency_ratio_irrational
    (by simpa only [hfreq] using heigen₁) (by simpa only [hfreq] using heigen₂)
  have hfactor := scalarCenter_spatialProduct_of_local_swaps M hM
    P.localSwaps P.unit_vector P.separating
  apply hClass (SpatialHilbert H K) (spatialProductAlgebra M P.algebra) hfactor
    (tensorVector P.vector Ω) _ (denseRange_spatialProduct_vector M P.algebra Ω P.vector
      hcyclic P.cyclic) hseparating m.group m.continuous hnormalizes m.isModular hcore
  rw [norm_tensorVector_apply, hΩ, P.unit_vector, mul_one]

end

end KadisonKastler

end OAI
