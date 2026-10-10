import OAI.Geometry.SurfaceImmersion.Geometry.CoefficientJetBounds
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicCoefficientProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.JetVelocityCoordinates

namespace OAI

/-! Second coefficient derivatives agree with the local represented jets,
even when only their germs agree after the first derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector JetPolynomial

lemma global_angle_eq_local_of_eqOn {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}
    (W : PeriodicExpansion.Family A E) (U : Family O E)
    (hW : ∀ p ∈ O, ∀ t : Period, W.val p t = U.val p t)
    {p : A} (hp : p ∈ O) (t : Period) : W.angle.val p t = U.angle.val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  rw [PeriodicExpansion.Family.angle_apply,Family.angle_apply U hp]
  have he : (fun z : A × ℝ => W.val z.1 (z.2 : Period)) =ᶠ[nhds (p,s)]
      (fun z => U.val z.1 (z.2 : Period)) := by
    filter_upwards [(O.isOpen.prod isOpen_univ).mem_nhds ⟨hp,mem_univ s⟩] with z hz
    exact hW z.1 hz.1 (z.2 : Period)
  exact congrArg (fun L : (A × ℝ) →L[ℝ] E => L (0,1)) he.fderiv_eq

def globalCoefficientDerivative (W : PeriodicExpansion.Family Base JetVelocityCoordinates.Euclidean)
    (k : Fin 3) : PeriodicExpansion.Family Base JetVelocityCoordinates.Euclidean :=
  ![W.slow (coordinateVector 0),W.slow (coordinateVector 1),W.angle] k

lemma global_coefficientDerivative_eq_local {S : TopologicalSpace.Opens Base}
    (W : PeriodicExpansion.Family Base JetVelocityCoordinates.Euclidean)
    (U : Family S JetVelocityCoordinates.Euclidean)
    (hW : ∀ p ∈ S, ∀ t : Period, W.val p t = U.val p t)
    (k : Fin 3) {p : Base} (hp : p ∈ S) (t : Period) :
    (globalCoefficientDerivative W k).val p t =
      (VectorExpression.coefficientFamilyDerivative U k).val p t := by
  fin_cases k
  · exact global_slow_eq_local_of_eqOn W U hW _ hp t
  · exact global_slow_eq_local_of_eqOn W U hW _ hp t
  · exact global_angle_eq_local_of_eqOn W U hW hp t

lemma global_second_coefficientDerivative_eq_local {S : TopologicalSpace.Opens Base}
    (W : PeriodicExpansion.Family Base JetVelocityCoordinates.Euclidean)
    (U : Family S JetVelocityCoordinates.Euclidean) (hW : W.val = U.val)
    (k j : Fin 3) {p : Base} (hp : p ∈ S) (t : Period) :
    (globalCoefficientDerivative (globalCoefficientDerivative W k) j).val p t =
      (VectorExpression.coefficientFamilyDerivative
        (VectorExpression.coefficientFamilyDerivative U k) j).val p t := by
  apply global_coefficientDerivative_eq_local _ _ _ j hp t
  intro q hq r
  exact global_coefficientDerivative_eq_local W U (by intro q _ t; rw [hW]) k hq r

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
