import OAI.Geometry.SurfaceImmersion.Primitive.UniformPrimitiveNormal
import OAI.Geometry.Immersion.ClosedSurface.ImmersionJets

namespace OAI

/-! The normal triple estimates imply the actual good phase and injective
differential in the plane coordinates used by the exact correction. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates SurfaceJetCoordinates

lemma primitiveNormalTriple_toEuclidean {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (p : JetPolynomial.Base) :
    primitiveNormalTriple (fun q => JetVelocityCoordinates.toEuclidean (G q)) p =
      ![slot 1 (lowJet G p),slot 2 (lowJet G p),slot 6 (lowJet G p)] := by
  have hy : (fun q => fderiv ℝ (fun r => JetVelocityCoordinates.toEuclidean (G r)) q
      (coordinateVector 1)) = fun q => JetVelocityCoordinates.toEuclidean (slot 2 (lowJet G q)) :=
    funext (euclidean_first_derivative hG 1)
  ext k a
  fin_cases k
  · change spaceCoordinates (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
      (coordinateVector 0)) a = _
    rw [euclidean_first_derivative hG]
    rfl
  · change spaceCoordinates (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
      (coordinateVector 1)) a = _
    rw [euclidean_first_derivative hG]
    rfl
  · change spaceCoordinates (fderiv ℝ
      (fun q => fderiv ℝ (fun r => JetVelocityCoordinates.toEuclidean (G r)) q
        (coordinateVector 1)) p (coordinateVector 1)) a = _
    rw [hy,euclidean_y_derivative hG]
    rfl

lemma primitiveNormalTriple_chart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : JetPolynomial.Base) :
    primitiveNormalTriple (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) p =
      ![realTwoJet F (baseEquiv p) 0,realTwoJet F (baseEquiv p) 1,
        realTwoJet F (baseEquiv p) 4] := by
  have he := primitiveNormalTriple_toEuclidean (hF.comp baseEquiv.contDiff) p
  simp only [Function.comp_apply] at he
  rw [he]
  have hh := decode_lowJet hF p
  ext k a
  fin_cases k
  · exact congrArg (fun J : CollarVelocity.JetBase => J.2 0 a) hh
  · exact congrArg (fun J : CollarVelocity.JetBase => J.2 1 a) hh
  · exact congrArg (fun J : CollarVelocity.JetBase => J.2 4 a) hh

theorem good_phase_of_primitive_normal {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : JetPolynomial.Base)
    (hD :
      let H := primitiveNormalTriple
        (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) p
      NormalFrame.gramDet (H 0) (H 1) ≠ 0)
    (hB :
      let H := primitiveNormalTriple
        (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) p
      realNormalPart (H 0) (H 1) (H 2) ≠ 0) :
    Function.Injective (fderiv ℝ F (baseEquiv p)) ∧
      PhaseGeometry.Good (realSecondTensor F (baseEquiv p)) SmallModes.dx := by
  dsimp only at hD hB
  rw [primitiveNormalTriple_chart hF] at hD hB
  change realSecondForm F SmallModes.dy SmallModes.dy (baseEquiv p) ≠ 0 at hB
  refine ⟨injective_of_gramDet_ne_zero _ hD,?_,?_⟩
  · intro hz
    exact one_ne_zero (congrArg Prod.fst hz)
  · simpa [PhaseGeometry.secondQuadratic,realSecondTensor,SmallModes.dx,SmallModes.dy] using hB

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
