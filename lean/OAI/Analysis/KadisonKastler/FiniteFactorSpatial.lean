import OAI.Analysis.KadisonKastler.PairedFactor
import OAI.Analysis.KadisonKastler.ConcreteUCP

namespace OAI

/-! # Spatial implementation of the nearby finite-factor isomorphism

The actual paired factor makes uniform amplification applicable on the
original Hilbert space. The published commutant-distance input and the
proved polar-intertwiner argument then produce the required unitary.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M N : VonNeumannAlgebra H}

local instance spatialFactorOrder {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : VonNeumannAlgebra K) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _

local instance spatialFactorStarOrder {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : VonNeumannAlgebra K) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

local instance spatialOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _

local instance spatialOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- A sufficiently close isomorphism between represented finite factors
is implemented by a nearby unitary, using the uniform amplification
theorem and the precise published commutant-distance input. -/
theorem finiteFactor_spatial_of_near_starEquiv
    (hpub : PublishedTracialUltrapower.{u})
    (hmat : PublishedFiniteMatrixUltraproduct)
    (hind : PublishedPopaFiniteBaseIndependence.{u})
    (hFock : PublishedDiagonalFockRepresentation.{u})
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (hCyclic : PublishedCyclicSimilarity.{u, u} (A := Algebra (pairedVonNeumann hM hN θ)))
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ < 1 / 2400)
    (hclose : ∀ x : Algebra M,
      ‖(x : H →L[ℂ] H) - (θ x : H →L[ℂ] H)‖ ≤ δ * ‖x‖) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ 2400 * δ := by
  let ρ := M.toStarSubalgebra.subtype
  let π := N.toStarSubalgebra.subtype.comp θ.toStarAlgHom
  have hcb := complete_closeness_of_finiteFactor_equiv hpub hmat hind
    hM hN θ hCyclic hFock hδ hclose
  obtain ⟨u, hu, hnorm⟩ := close_representations_of_published hCommutant ρ π
    (by positivity : 0 ≤ 600 * δ) (by linarith : 600 * δ < 1 / 4) hcb
  refine ⟨u, conjugates_of_starEquiv θ u hu, ?_⟩
  linarith

end

end KadisonKastler

end OAI
