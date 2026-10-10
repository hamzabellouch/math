import OAI.Analysis.KadisonKastler.SpatialTensorDescent

namespace OAI

/-! # Quantitative removal of a fixed auxiliary factor -/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance tensorModulusAlgebraOrder (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance tensorModulusAlgebraStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

/-- The auxiliary tolerance used before choosing any representation or algebra. -/
def spatialDescentTolerance (ε : ℝ) : ℝ := min (ε / 512) (1 / 4000)

theorem spatialDescentTolerance_pos {ε : ℝ} (hε : 0 < ε) :
    0 < spatialDescentTolerance ε := by
  unfold spatialDescentTolerance
  positivity

/-- A sufficiently small spatial-product conjugacy gives a conjugacy of the
original pair, with the prescribed strict displacement. -/
theorem nearConjugacy_of_spatial_product
    {M N : VonNeumannAlgebra H} (D : VonNeumannAlgebra K)
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (ξ : K) (hξ : ‖ξ‖ = 1) {ε : ℝ} (hε : 0 < ε)
    (hgap : kkDistance M N < 1 / 4)
    (h : NearConjugacy (spatialProductAlgebra M D) (spatialProductAlgebra N D)
      (spatialDescentTolerance ε)) : NearConjugacy M N ε := by
  obtain ⟨z, hz, hnorm⟩ := h
  have htol : spatialDescentTolerance ε ≤ 1 / 4000 := min_le_right _ _
  have hsmall : 2 * ‖(z : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) - 1‖ <
      1 / 1000 := by linarith
  obtain ⟨u, hu, hbound⟩ := concrete_unitary_of_spatial_product_conjugacy D
    hCorrection hCommutant ξ hξ z hz hgap hsmall (by linarith)
  refine ⟨u, hu, ?_⟩
  have hεtol : spatialDescentTolerance ε ≤ ε / 512 := min_le_left _ _
  linarith

end

end KadisonKastler

end OAI
