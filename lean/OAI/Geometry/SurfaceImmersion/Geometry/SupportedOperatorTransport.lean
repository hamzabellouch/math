import OAI.Geometry.SurfaceImmersion.Atlas.SupportedCoordinateChange

namespace OAI

/-! Transport of differential operators through a fixed isometric coordinate
change, including their finite derivative-loss estimates. -/
noncomputable section
open TopologicalSpace
open scoped NNReal

namespace ClosedSurfaceR4.JetPolynomial

variable {A B F G : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def transportSupportedLM (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A)
    (L : SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := G) K) :
    SupportedField (F := F) (K.map e e.continuous) →ₗ[ℝ]
      SupportedField (F := G) (K.map e e.continuous) :=
  (supportedCoordinateEquiv e K).toLinearMap.comp
    (L.comp (supportedCoordinateEquiv e K).symm.toLinearMap)

lemma transportSupportedLM_bound (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A)
    (L : SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := G) K)
    {s : ℝ≥0} (hs : 0 < (s : ℝ)) (m r : ℕ) (C : ℝ)
    (hL : ∀ f, supportedWeightedSeminorm K s m (L f) ≤ C * supportedWeightedSeminorm K s r f)
    (f : SupportedField (F := F) (K.map e e.continuous)) :
    supportedWeightedSeminorm (K.map e e.continuous) s m (transportSupportedLM e K L f) ≤
      C * supportedWeightedSeminorm (K.map e e.continuous) s r f := by
  change supportedWeightedSeminorm (K.map e e.continuous) s m
    (supportedCoordinateEquiv e K (L ((supportedCoordinateEquiv e K).symm f))) ≤ _
  rw [supportedCoordinateEquiv_norm e K hs]
  calc
    _ ≤ C * supportedWeightedSeminorm K s r ((supportedCoordinateEquiv e K).symm f) := hL _
    _ = _ := by
      have he := supportedCoordinateEquiv_norm e K hs r ((supportedCoordinateEquiv e K).symm f)
      rw [LinearEquiv.apply_symm_apply] at he
      rw [he]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
