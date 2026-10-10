import OAI.Analysis.IrrationalRotation.Rotation.RotationTrace
import OAI.Analysis.IrrationalRotation.Rotation.RotationAlgebra
import OAI.Analysis.IrrationalRotation.Spectral.RotationDeterminant
import OAI.Analysis.IrrationalRotation.Spectral.VectorSpectral

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.Rotation

def vacuumTracialState (θ : ℝ) : TracialState (algebra θ) :=
  (vacuum_faithfulTracial θ).toTracialState

@[simp] theorem vacuumTracialState_apply (θ : ℝ) (A : algebra θ) :
    vacuumTracialState θ A = vectorTrace vacuum (A : Hilbert →L[ℂ] Hilbert) := rfl

theorem vacuumTracialState_determinant_eq_vector (θ : ℝ) (A : algebra θ) :
    fugledeKadisonDeterminant (vacuumTracialState θ) A =
      vectorFugledeKadisonDeterminant vacuum (A : Hilbert →L[ℂ] Hilbert) :=
  (vacuum_faithfulTracial θ).determinant_eq_vector A

theorem vacuumTracialState_weightedReal_determinant_zero
    (θ : ℝ) (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    fugledeKadisonDeterminant (vacuumTracialState θ)
      ⟨weightedReal θ f, weightedReal_mem_algebra θ f⟩ = 0 := by
  rw [vacuumTracialState_determinant_eq_vector]
  exact weightedReal_vectorDeterminant_zero θ f hf

theorem exists_tracialState_weightedReal_determinant_zero
    (θ : ℝ) (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    ∃ τ : TracialState (algebra θ),
      (∀ A : algebra θ, τ A = vectorTrace vacuum (A : Hilbert →L[ℂ] Hilbert)) ∧
      ∃ T : algebra θ, (T : Hilbert →L[ℂ] Hilbert) = weightedReal θ f ∧
        fugledeKadisonDeterminant τ T = 0 := by
  refine ⟨vacuumTracialState θ, vacuumTracialState_apply θ,
    ⟨weightedReal θ f, weightedReal_mem_algebra θ f⟩, rfl, ?_⟩
  exact vacuumTracialState_weightedReal_determinant_zero θ f hf

theorem weightedReal_algebra_normQuasinilpotent
    (θ : ℝ) (hθ : Irrational θ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    NormQuasinilpotent (⟨weightedReal θ f, weightedReal_mem_algebra θ f⟩ : algebra θ) := by
  have hn (n : ℕ) :
      ‖(⟨weightedReal θ f, weightedReal_mem_algebra θ f⟩ : algebra θ) ^ n‖ =
        ‖weightedReal θ f ^ n‖ := by
    change ‖(algebra θ).toStarSubalgebra.subtype
      ((⟨weightedReal θ f, weightedReal_mem_algebra θ f⟩ : algebra θ) ^ n)‖ = _
    rw [map_pow]
    rfl
  unfold NormQuasinilpotent
  simp_rw [hn]
  exact weightedReal_normQuasinilpotent hθ f hf

theorem weightedReal_algebra_spectrum
    (θ : ℝ) (hθ : Irrational θ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    spectrum ℂ (⟨weightedReal θ f, weightedReal_mem_algebra θ f⟩ : algebra θ) = {0} :=
  spectrum_eq_zero_of_norm_root_tendsto_zero _
    (weightedReal_algebra_normQuasinilpotent θ hθ f hf)

theorem exists_tracialState_weightedReal_spectral_bundle
    (θ : ℝ) (hθ : Irrational θ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    ∃ τ : TracialState (algebra θ),
      (∀ A : algebra θ, τ A = vectorTrace vacuum (A : Hilbert →L[ℂ] Hilbert)) ∧
      ∃ T : algebra θ, (T : Hilbert →L[ℂ] Hilbert) = weightedReal θ f ∧
        T ≠ 0 ∧ NormQuasinilpotent T ∧ spectrum ℂ T = {0} ∧
        fugledeKadisonDeterminant τ T = 0 := by
  refine ⟨vacuumTracialState θ, vacuumTracialState_apply θ,
    ⟨weightedReal θ f, weightedReal_mem_algebra θ f⟩, rfl, ?_,
    weightedReal_algebra_normQuasinilpotent θ hθ f hf,
    weightedReal_algebra_spectrum θ hθ f hf,
    vacuumTracialState_weightedReal_determinant_zero θ f hf⟩
  intro hz
  exact weightedReal_ne_zero_of_isContinuousCircleWeight θ f hf (congrArg Subtype.val hz)

theorem vacuumTracialState_isBrownMeasure_iff_vector
    (θ : ℝ) (A : algebra θ) (μ : Measure ℂ) :
    IsBrownMeasure (vacuumTracialState θ) A μ ↔
      IsVectorBrownMeasure vacuum (A : Hilbert →L[ℂ] Hilbert) μ :=
  (vacuum_faithfulTracial θ).isBrownMeasure_iff_vector A μ

end Invariant233.Rotation

end

end OAI
