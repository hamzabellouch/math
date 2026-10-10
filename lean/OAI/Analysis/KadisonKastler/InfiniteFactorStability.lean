import OAI.Analysis.KadisonKastler.FixedFactorPublishedInputs
import OAI.Analysis.KadisonKastler.FixedTensorAbsorption
import OAI.Analysis.KadisonKastler.ExpectedModelStability
import OAI.Analysis.KadisonKastler.FactorStability
import OAI.Analysis.KadisonKastler.TypeIMatrixPreparation
import OAI.Analysis.KadisonKastler.SpatialTensorModulus
import OAI.Analysis.KadisonKastler.SpatialCompleteGap
import OAI.Analysis.KadisonKastler.SpatialMatrixGap
import OAI.Analysis.KadisonKastler.SpatialSeparability

namespace OAI

/-! # Uniform strong stability for properly infinite factors

The auxiliary product is fixed before any tolerance or representation is
chosen. Matrix preparation gives complete proximity, which passes to the
spatial product. Expected-subfactor stability is then descended to the
original Hilbert space. Every published assumption is in the named bundle.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

local instance infiniteStabilityOrder {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (M : VonNeumannAlgebra K) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance infiniteStabilityStarOrder {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (M : VonNeumannAlgebra K) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

private theorem productStage_size_pos
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K] (P : ProductMatrixStages (H := K)) (n : ℕ) : 0 < P.size n := by
  by_contra h
  have hz : P.size n = 0 := Nat.eq_zero_of_not_pos h
  let : IsEmpty (Fin (P.size n)) := ⟨fun i => by have := i.isLt; omega⟩
  have he : (0 : K →L[ℂ] K) = 1 := by simpa using (P.matrix n).total
  exact zero_ne_one he

/-- The properly infinite factor case, with a uniform modulus and no
cyclic-vector or common-subfactor hypothesis on the original pair. -/
theorem uniform_properlyInfinite_strong_stability_of_product_models
    (h : ModularCorePublishedInputs.{u})
    (hmod : PublishedModularSpectralResolution.{u})
    (hclass : PublishedFactorialModularCore.{u})
    (hkap : PublishedKaplanskyDensity.{u})
    (P : TwoRatioProductModel.{u})
    (hexpected : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H]
      (M : VonNeumannAlgebra H), ScalarCenter M →
      Nonempty (ExpectedMatrixSubfactorModel (spatialProductAlgebra M P.stages.algebra))) :
    UniformProperInfiniteFactorStability.{u} := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨t, ht, hstable⟩ := uniform_expected_models_typeIII1_stability
    h hmod
    (spatialDescentTolerance_pos hhalf)
  let δ := min (1 / 2000 : ℝ) (min (t / 604) (min (1 / 2408) (ε / 600)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ₁ : δ ≤ 1 / 2000 := min_le_left _ _
  have hδt : δ ≤ t / 604 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₂ : δ ≤ 1 / 2408 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδε : δ ≤ ε / 600 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  intro H _ _ _ _ _ M N hM hN hMinf hgap
  obtain ⟨a, ha, hgap₁, hMN, hNM⟩ := exists_properInfinite_matrix_preparation_of_embedding
    M N hMinf (by linarith : δ ≤ 1 / 1152) hgap
  let N₁ := unitaryConjugateAlgebra (star a) N
  have hN₁ : ScalarCenter N₁ :=
    hN.of_starAlgEquiv (unitaryConjugateEquiv (star a) N)
  have hMtype := P.tensor_typeIII1_general hmod hkap h.realSpectral h.diagonal hclass H M hM
  have hNtype := P.tensor_typeIII1_general hmod hkap h.realSpectral h.diagonal hclass H N₁ hN₁
  obtain ⟨E⟩ := hexpected H M hM
  obtain ⟨F⟩ := hexpected H N₁ hN₁
  have hnonneg : 0 ≤ 301 * δ := by positivity
  have hs : ∀ n, 0 < P.stages.size n := productStage_size_pos P.stages
  have hprodMN := hMN.spatialProduct (E := P.stages.matrix) hkap
    hnonneg hs P.stages.increasing
  have hprodNM := hNM.spatialProduct (E := P.stages.matrix) hkap
    hnonneg hs P.stages.increasing
  have hprodgap := kkDistance_spatialProduct_le_of_matrixNearInclusion
    (E := P.stages.matrix) hkap M N₁ hnonneg hMN hNM hs P.stages.increasing
  have hprod : NearConjugacy (spatialProductAlgebra M P.stages.algebra)
      (spatialProductAlgebra N₁ P.stages.algebra) (spatialDescentTolerance (ε / 2)) :=
    hstable (SpatialHilbert H P.K) _ _ hMtype hNtype E F (302 * δ)
      (by positivity) (by linarith) (by exact hprodgap.trans_lt (by linarith))
      (hprodMN.mono (by linarith)) (hprodNM.mono (by linarith))
  have hdown : NearConjugacy M N₁ (ε / 2) := nearConjugacy_of_spatial_product
    P.stages.algebra (h.correction H M)
    (publishedBlockCommutantApproximation (Algebra M) H) P.stages.vector
    P.stages.unit_vector hhalf (by dsimp [N₁]; linarith) hprod
  obtain ⟨v, hv, hnorm⟩ := hdown
  refine ⟨a * v, conjugates_of_conjugated_neighbor a v hv, ?_⟩
  exact (norm_unitary_mul_sub_one_le a v).trans_lt (by linarith)

/-- The original published-input theorem is preserved as a specialization. -/
theorem uniform_properlyInfinite_strong_stability
    (h : FixedFactorPublishedInputs.{u}) : UniformProperInfiniteFactorStability.{u} := by
  obtain ⟨P⟩ := h.product
  apply uniform_properlyInfinite_strong_stability_of_product_models
    h.toModularCorePublishedInputs h.modular h.coreClassification h.kaplansky P
  intro H _ _ _ _ _ M hM
  obtain ⟨R,hR⟩ := P.tensor_absorbs_powers h.pointed h.kaplansky H M
  exact h.expected (SpatialHilbert H P.K) (spatialProductAlgebra M P.stages.algebra)
    (P.typeIII1_of_published h H M hM) R hR

end

end KadisonKastler

end OAI
