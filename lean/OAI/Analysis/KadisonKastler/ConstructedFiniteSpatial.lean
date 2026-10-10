import OAI.Analysis.KadisonKastler.ConstructedPairedAmplification
import OAI.Analysis.KadisonKastler.BlockCommutantConstruction
import OAI.Analysis.KadisonKastler.ConcreteUCP

namespace OAI

/-! # Spatial implementation using the constructed finite-factor estimate -/

namespace KadisonKastler
noncomputable section
universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M N : VonNeumannAlgebra H}

local instance constructedFiniteSpatialSourceOrder (P : VonNeumannAlgebra H) : PartialOrder (Algebra P) :=
  CStarAlgebra.spectralOrder _
local instance constructedFiniteSpatialSourceStarOrder (P : VonNeumannAlgebra H) : StarOrderedRing (Algebra P) :=
  CStarAlgebra.spectralOrderedRing _
local instance constructedFiniteSpatialOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance constructedFiniteSpatialOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance constructedFiniteSpatialPairOrder
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    PartialOrder (Algebra (pairedVonNeumann hM hN θ)) := CStarAlgebra.spectralOrder _
local instance constructedFiniteSpatialPairStarOrder
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    StarOrderedRing (Algebra (pairedVonNeumann hM hN θ)) := CStarAlgebra.spectralOrderedRing _

/-- The concrete paired factor gives the required complete bound. -/
theorem constructed_complete_closeness_of_finiteFactor_equiv
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ x : Algebra M, ‖x.val - (θ x).val‖ ≤ δ * ‖x‖) :
    CompletelyBoundedBy (M.toStarSubalgebra.subtype.toLinearMap -
      (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom).toAlgHom.toLinearMap)
      (1000000 * δ) := by
  exact constructed_complete_closeness_of_paired_factor
    (pairedVonNeumann_isII1 hM hN θ)
    M.toStarSubalgebra.subtype (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom)
    (pairedFactorEquiv hM hN θ) (pairedFactorEquiv_apply hM hN θ) hδ hclose

/-- A nearby finite-factor isomorphism is spatial, with no published
amplification or commutant-distance assumption. -/
theorem constructed_finiteFactor_spatial_of_near_starEquiv
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ < 1 / 4000000)
    (hclose : ∀ x : Algebra M,
      ‖x.val - (θ x).val‖ ≤ δ * ‖x‖) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ 4000000 * δ := by
  let ρ := M.toStarSubalgebra.subtype
  let π := N.toStarSubalgebra.subtype.comp θ.toStarAlgHom
  have hcb := constructed_complete_closeness_of_finiteFactor_equiv hM hN θ hδ hclose
  obtain ⟨u, hu, hnorm⟩ := close_representations_of_published
    (publishedBlockCommutantApproximation (Algebra M) H) ρ π
    (by positivity : 0 ≤ 1000000 * δ) (by linarith : 1000000 * δ < 1 / 4) hcb
  exact ⟨u, conjugates_of_starEquiv θ u hu, by linarith⟩

end
end KadisonKastler

end OAI
