import OAI.Analysis.IrrationalRotation.Model.ConcreteSpectral
import OAI.Analysis.IrrationalRotation.Operators.VectorTraceState
import OAI.Analysis.IrrationalRotation.Spectral.SpectralNaturality

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem IsFaithfulTracialVector.determinant_eq_vector
    {M : VonNeumannAlgebra H} {ξ : H} (h : IsFaithfulTracialVector M ξ) (a : M) :
    fugledeKadisonDeterminant h.toTracialState a =
      vectorFugledeKadisonDeterminant ξ (a : H →L[ℂ] H) := by
  unfold fugledeKadisonDeterminant vectorFugledeKadisonDeterminant
  apply iInf_congr
  intro ε
  have hmap : ((CFC.log (star a * a + ε.val • (1 : M)) : M) : H →L[ℂ] H) =
      CFC.log (star (a : H →L[ℂ] H) * (a : H →L[ℂ] H) + ε.val • (1 : H →L[ℂ] H)) :=
    regularizedLog_map M.toStarSubalgebra.subtype a ε.val ε.property
  change ENNReal.ofReal (Real.exp ((vectorTrace ξ
    ((CFC.log (star a * a + ε.val • (1 : M)) : M) : H →L[ℂ] H)).re / 2)) = _
  rw [hmap]

theorem IsFaithfulTracialVector.isBrownMeasure_iff_vector
    {M : VonNeumannAlgebra H} {ξ : H} (h : IsFaithfulTracialVector M ξ)
    (a : M) (μ : Measure ℂ) :
    IsBrownMeasure h.toTracialState a μ ↔
      IsVectorBrownMeasure ξ (a : H →L[ℂ] H) μ := by
  unfold IsBrownMeasure IsVectorBrownMeasure
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro z
  rw [h.determinant_eq_vector]
  rfl

theorem vectorFugledeKadisonDeterminant_of_continuous_integration
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    (μ : Measure X) (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hξ : ∀ g : C(X, ℂ), vectorTrace ξ (π g) = ∫ x, g x ∂μ) (f : C(X, ℂ)) :
    vectorFugledeKadisonDeterminant ξ (π f) =
      ⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (‖f x‖ ^ 2 + ε.val) ∂μ) / 2)) := by
  let : NormedAlgebra ℝ C(X, ℂ) := NormedAlgebra.restrictScalars ℝ ℂ C(X, ℂ)
  unfold vectorFugledeKadisonDeterminant
  apply iInf_congr
  intro ε
  rw [← regularizedLog_map π f ε.val ε.property, hξ]
  have hpoint : ∀ x, (CFC.log (star f * f + ε.val • (1 : C(X, ℂ)))) x =
      (Real.log (‖f x‖ ^ 2 + ε.val) : ℂ) := by
    intro x
    have h := regularizedLog_map (ContinuousMap.evalStarAlgHom ℂ ℂ x) f ε.val ε.property
    simpa only [ContinuousMap.evalStarAlgHom_apply] using
      h.trans (regularizedLog_complex (f x) ε.val)
  simp_rw [hpoint]
  rw [integral_complex_ofReal]
  rfl

theorem vectorFugledeKadisonDeterminant_isometry_mul (ξ : H)
    (u a : H →L[ℂ] H) (hu : star u * u = 1) :
    vectorFugledeKadisonDeterminant ξ (u * a) = vectorFugledeKadisonDeterminant ξ a := by
  have h : star (u * a) * (u * a) = star a * a := by
    rw [star_mul, mul_assoc, ← mul_assoc (star u), hu]
    simp
  simp only [vectorFugledeKadisonDeterminant, h]

end Invariant233

end

end OAI
