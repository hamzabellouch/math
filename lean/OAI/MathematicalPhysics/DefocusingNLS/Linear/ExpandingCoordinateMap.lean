import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousYLocalization

namespace OAI

/-! # Finite coordinates of localized torus data -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def expandingCoordinates (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ))
    (π : HomogeneousY a k →L[ℝ] F) (L : {L : ℝ // 1 ≤ L}) : FourierL2 →L[ℝ] F :=
  π.comp ((homogeneousLocalizationCLM a k L.1 ha ha1 hk L.2 χ).restrictScalars ℝ)

@[simp] theorem expandingCoordinates_apply (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ))
    (π : HomogeneousY a k →L[ℝ] F) (L : {L : ℝ // 1 ≤ L}) (f : FourierL2) :
    expandingCoordinates a k ha ha1 hk χ π L f =
      π (homogeneousLocalizationCLM a k L.1 ha ha1 hk L.2 χ f) := rfl

theorem expandingCoordinates_norm_le (a k C : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hC : 0 ≤ C) (χ : 𝓢(E, ℂ))
    (π : HomogeneousY a k →L[ℝ] F)
    (hCb : ∀ (L : ℝ) (hL : 1 ≤ L) (f : FourierL2),
      ‖homogeneousLocalizationCLM a k L ha ha1 hk hL χ f‖ ≤ C * ‖f‖)
    (L : {L : ℝ // 1 ≤ L}) : ‖expandingCoordinates a k ha ha1 hk χ π L‖ ≤ ‖π‖ * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) hC)
  intro f
  calc
    _ ≤ ‖π‖ * ‖homogeneousLocalizationCLM a k L.1 ha ha1 hk L.2 χ f‖ := π.le_opNorm _
    _ ≤ ‖π‖ * (C * ‖f‖) := mul_le_mul_of_nonneg_left (hCb L.1 L.2 f) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end DefocusingNLS

end OAI
