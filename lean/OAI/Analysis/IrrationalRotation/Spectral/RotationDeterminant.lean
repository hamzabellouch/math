import OAI.Analysis.IrrationalRotation.Model.ConcreteSpectral
import OAI.Analysis.IrrationalRotation.Rotation.Rotation
import OAI.Analysis.IrrationalRotation.Rotation.RotationDiagonalState
import OAI.Analysis.IrrationalRotation.Spectral.RotationQuasinilpotent
import OAI.Analysis.IrrationalRotation.Spectral.DeterminantWeightBridge

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal CStarAlgebra
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorFugledeKadisonDeterminant_unitary_mul (ξ : H)
    (u : unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    vectorFugledeKadisonDeterminant ξ ((u : H →L[ℂ] H) * T) =
      vectorFugledeKadisonDeterminant ξ T := by
  have h : star ((u : H →L[ℂ] H) * T) * ((u : H →L[ℂ] H) * T) = star T * T := by
    rw [star_mul, mul_assoc, ← mul_assoc (star (u : H →L[ℂ] H)),
      Unitary.star_mul_self_of_mem u.property]
    simp
  simp only [vectorFugledeKadisonDeterminant, h]

theorem vectorFugledeKadisonDeterminant_continuous_representation
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    (μ : Measure X) (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hξ : ∀ g : C(X, ℂ), vectorTrace ξ (π g) = ∫ x, g x ∂μ)
    (f : C(X, ℂ)) :
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

namespace Rotation

theorem representation_real_vectorDeterminant_zero (θ : ℝ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    vectorFugledeKadisonDeterminant vacuum (representation θ (complexWeight f)) = 0 := by
  have hformula := vectorFugledeKadisonDeterminant_continuous_representation
    circleMeasure (representationStarAlgHom θ) vacuum
    (fun g => vacuumFunctional_representation θ g) (complexWeight f)
  change vectorFugledeKadisonDeterminant vacuum (representation θ (complexWeight f)) = _
    at hformula
  rw [hformula]
  have hnorm : ∀ x, ‖complexWeight f x‖ = f x := by
    intro x
    simp only [complexWeight, ContinuousMap.coe_mk, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hf.2.1 x).1]
  simp_rw [hnorm]
  exact hf.regularized_determinant_eq_zero

theorem weightedReal_vectorDeterminant_zero (θ : ℝ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    vectorFugledeKadisonDeterminant vacuum (weightedReal θ f) = 0 := by
  let u : unitary (Hilbert →L[ℂ] Hilbert) := ⟨U, U_mem_unitary⟩
  change vectorFugledeKadisonDeterminant vacuum
    ((u : Hilbert →L[ℂ] Hilbert) * representation θ (complexWeight f)) = 0
  rw [vectorFugledeKadisonDeterminant_unitary_mul]
  exact representation_real_vectorDeterminant_zero θ f hf

theorem continuous_weight_spectral_bundle (θ : ℝ) (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    weightedReal θ f ≠ 0 ∧ NormQuasinilpotent (weightedReal θ f) ∧
      vectorFugledeKadisonDeterminant vacuum (weightedReal θ f) = 0 :=
  ⟨weightedReal_ne_zero_of_isContinuousCircleWeight θ f hf,
    weightedReal_normQuasinilpotent hθ f hf, weightedReal_vectorDeterminant_zero θ f hf⟩

end Rotation
end Invariant233

end

end OAI
