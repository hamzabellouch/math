import OAI.Analysis.KadisonKastler.SpatialSlice
import OAI.Analysis.KadisonKastler.HilbertCompression
import OAI.Analysis.KadisonKastler.UCPDescent

namespace OAI

/-! # Removing the auxiliary spatial tensor factor

A concrete unit vector slice removes the auxiliary factor. Thus an upstairs
unitary yields an original-space unitary with the explicit UCP descent bound.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped CStarAlgebra

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance tensorDescentOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance tensorDescentStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

local instance tensorDescentAlgebraOrder (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance tensorDescentAlgebraStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

/-- The concrete vector slice is completely positive. -/
def tensorVectorSliceCP (ξ : K) :
    (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) →CP (H →L[ℂ] H) :=
  hilbertCompressionCP (tensorVector ξ)

omit [CompleteSpace K] in
@[simp]
theorem tensorVectorSliceCP_apply (ξ : K)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :
    tensorVectorSliceCP ξ T = tensorVectorSlice ξ T := rfl

/-- A unit vector makes the first-leg representation faithful. -/
theorem spatialLeft_injective_of_unit_vector (ξ : K) (hξ : ‖ξ‖ = 1) :
    Function.Injective (spatialLeft (H := H) (K := K)) := by
  intro a b hab
  have h := congrArg (tensorVectorSlice ξ) hab
  simpa only [tensorVectorSlice_spatialLeft ξ hξ] using h

/-- The tensor-factor removal estimate, on the original Hilbert space. -/
theorem concrete_unitary_of_spatial_product_conjugacy
    {M N : VonNeumannAlgebra H} (D : VonNeumannAlgebra K)
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (ξ : K) (hξ : ‖ξ‖ = 1)
    (z : unitary (SpatialHilbert H K →L[ℂ] SpatialHilbert H K))
    (hz : Conjugates z (spatialProductAlgebra M D) (spatialProductAlgebra N D))
    {g : ℝ} (hgap : kkDistance M N < g)
    (hsmall : 2 * ‖(z : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) - 1‖ < 1 / 1000)
    (hge : g + 2 * ‖(z : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) - 1‖ < 1) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤
        256 * ‖(z : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) - 1‖ := by
  have hE : tensorVectorSliceCP (H := H) ξ 1 = 1 := by
    rw [← map_one (spatialLeft (H := H) (K := K))]
    exact tensorVectorSlice_spatialLeft ξ hξ 1
  have hfix : ∀ x : H →L[ℂ] H, tensorVectorSliceCP ξ (spatialLeft (K := K) x) = x :=
    fun x => tensorVectorSlice_spatialLeft ξ hξ x
  apply concrete_unitary_of_retracted_conjugation hCorrection hCommutant
    (spatialLeft (H := H) (K := K)) (spatialLeft_injective_of_unit_vector ξ hξ)
    (tensorVectorSliceCP ξ) hE hfix z _ hgap hsmall hge
  intro x
  apply tensorVectorSlice_mem N D ξ
  change unitaryConj z (spatialLeft (K := K) (x : H →L[ℂ] H)) ∈
    (spatialProductAlgebra N D : Set
      (SpatialHilbert H K →L[ℂ] SpatialHilbert H K))
  rw [← hz]
  exact ⟨spatialLeft (K := K) (x : H →L[ℂ] H),
    spatialLeft_mem_product M D x.property, rfl⟩

end

end KadisonKastler

end OAI
