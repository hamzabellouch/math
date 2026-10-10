import OAI.Analysis.IrrationalRotation.Operators.VectorTraceNormality
import OAI.Analysis.IrrationalRotation.Spectral.RotationTracialDeterminant

namespace OAI

noncomputable section
namespace Invariant233.Rotation

theorem vacuumTracialState_normal (θ : ℝ) :
    IsNormalFaithfulTracialState (algebra θ) (vacuumTracialState θ) :=
  (vacuum_faithfulTracial θ).toTracialState_normal

theorem exists_normalTracialState_weightedReal_determinant_zero
    (θ : ℝ) (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    ∃ τ : TracialState (algebra θ),
      IsNormalFaithfulTracialState (algebra θ) τ ∧
      (∀ A : algebra θ, τ A = vectorTrace vacuum (A : Hilbert →L[ℂ] Hilbert)) ∧
      ∃ T : algebra θ, (T : Hilbert →L[ℂ] Hilbert) = weightedReal θ f ∧
        fugledeKadisonDeterminant τ T = 0 := by
  refine ⟨vacuumTracialState θ, vacuumTracialState_normal θ,
    vacuumTracialState_apply θ,
    ⟨weightedReal θ f, weightedReal_mem_algebra θ f⟩, rfl, ?_⟩
  exact vacuumTracialState_weightedReal_determinant_zero θ f hf

theorem exists_normalTracialState_weightedReal_spectral_bundle
    (θ : ℝ) (hθ : Irrational θ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    ∃ τ : TracialState (algebra θ),
      IsNormalFaithfulTracialState (algebra θ) τ ∧
      (∀ A : algebra θ, τ A = vectorTrace vacuum (A : Hilbert →L[ℂ] Hilbert)) ∧
      ∃ T : algebra θ, (T : Hilbert →L[ℂ] Hilbert) = weightedReal θ f ∧
        T ≠ 0 ∧ NormQuasinilpotent T ∧ spectrum ℂ T = {0} ∧
        fugledeKadisonDeterminant τ T = 0 := by
  refine ⟨vacuumTracialState θ, vacuumTracialState_normal θ,
    vacuumTracialState_apply θ,
    ⟨weightedReal θ f, weightedReal_mem_algebra θ f⟩, rfl, ?_,
    weightedReal_algebra_normQuasinilpotent θ hθ f hf,
    weightedReal_algebra_spectrum θ hθ f hf,
    vacuumTracialState_weightedReal_determinant_zero θ f hf⟩
  intro hz
  exact weightedReal_ne_zero_of_isContinuousCircleWeight θ f hf (congrArg Subtype.val hz)

end Invariant233.Rotation

end

end OAI
