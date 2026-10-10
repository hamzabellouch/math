import OAI.Geometry.CylinderCovering.Beams.NeighborhoodCoversDefinitions
import OAI.Geometry.CylinderCovering.Convexity.SimilarityDefinitions

namespace OAI

noncomputable section
open Set
namespace ShortenedBeam
open CylinderCovering

def TransportedNeighborhoodFamilies (a : ℝ) (N : ℕ) (t : Space) (r : ℝ)
    (L : Space ≃ₗᵢ[ℝ] Space)
    (Cm Cp : Fin N → RuledApproximation.Cylinder) : Prop :=
  (∀ i : Fin N,
    (Cm i).axis = L (axisMinus a (midpointTag N i)) ∧
    (Cp i).axis = L (axisPlus a (midpointTag N i)) ∧
    Subtype.val '' (Cm i).base =
      Similarity.transportedBase (neighborhoodBaseMinus a N i)
        (axisMinus a (midpointTag N i)) t r L ∧
    Subtype.val '' (Cp i).base =
      Similarity.transportedBase (neighborhoodBasePlus a N i)
        (axisPlus a (midpointTag N i)) t r L ∧
    IsCompact (Cm i).base ∧ IsCompact (Cp i).base) ∧
  Similarity.map t r L '' beamMinus a ⊆ RuledApproximation.familySet Cm ∧
  Similarity.map t r L '' beamPlus a ⊆ RuledApproximation.familySet Cp

def RegularNeighborhoodStatement : Prop :=
  ∀ K : Set Space, IsRegularTetrahedron K →
    ∃ a : ℝ, 0 < a ∧ a < 1/2 ∧
    ∃ t : Space, ∃ r : ℝ, ∃ L : Space ≃ₗᵢ[ℝ] Space,
      0 < r ∧ K = Similarity.map t r L '' tetrahedron ∧
      ∃ N : ℕ, 0 < N ∧
      ∃ Cm Cp : Fin N → RuledApproximation.Cylinder,
      ∃ n : ℕ, ∃ D : Fin n → RuledApproximation.Cylinder,
        TransportedNeighborhoodFamilies a N t r L Cm Cp ∧
        (∀ j, BeamStrip.HasRectangularBase (D j) ∧ IsCompact (D j).base) ∧
        Similarity.map t r L '' strip a ⊆ RuledApproximation.familySet D ∧
        K ⊆ (RuledApproximation.familySet Cm ∪ RuledApproximation.familySet Cp) ∪
          RuledApproximation.familySet D ∧
        RuledApproximation.familyArea Cm + RuledApproximation.familyArea Cp +
          RuledApproximation.familyArea D < minimumShadowArea K/2

end ShortenedBeam

end

end OAI
