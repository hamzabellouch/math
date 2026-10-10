import OAI.Geometry.SurfaceImmersion.Correction.PolynomialModeResidual

namespace OAI

/-! Transfer compact phase supports between the two plane coordinate conventions. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

def jetSupport (K : Compacts SmallModes.Base) : Compacts Base :=
  K.map planeCoordinateIsometry.symm planeCoordinateIsometry.symm.continuous

@[simp] lemma modeSupport_jetSupport (K : Compacts SmallModes.Base) :
    modeSupport (jetSupport K) = K := by
  apply SetLike.coe_injective
  change planeCoordinateIsometry '' (planeCoordinateIsometry.symm '' (K : Set SmallModes.Base)) = K
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    simpa only [planeCoordinateIsometry.apply_symm_apply] using hz
  · intro hx
    exact ⟨planeCoordinateIsometry.symm x,⟨x,hx,rfl⟩,
      planeCoordinateIsometry.apply_symm_apply x⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The function is unchanged; only its compact-support index is transferred. -/
def onModeSupport (K : Compacts SmallModes.Base) (f : SupportedField (F := E) K) :
    SupportedField (F := E) (modeSupport (jetSupport K)) :=
  ⟨f, f.contDiff, fun x hx => f.zero_on_compl (by simpa only [modeSupport_jetSupport] using hx)⟩

@[simp] lemma onModeSupport_apply (K : Compacts SmallModes.Base)
    (f : SupportedField (F := E) K) (x : SmallModes.Base) : onModeSupport K f x = f x := rfl

def onModeSupportLM (K : Compacts SmallModes.Base) :
    SupportedField (F := E) K →ₗ[ℝ] SupportedField (F := E) (modeSupport (jetSupport K)) where
  toFun := onModeSupport K
  map_add' _ _ := by apply DFunLike.ext; intro x; rfl
  map_smul' _ _ := by apply DFunLike.ext; intro x; rfl

lemma onModeSupport_seminorm (K : Compacts SmallModes.Base) (s : ℝ≥0)
    (hs : 0 < (s : ℝ)) (m : ℕ) (f : SupportedField (F := E) K) :
    supportedWeightedSeminorm (modeSupport (jetSupport K)) s m (onModeSupport K f) =
      supportedWeightedSeminorm K s m f := by
  apply le_antisymm
  · exact supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _)
      (onModeSupport K f) (weightedBound_of_supportedSeminorm s m f)
  · exact supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _)
      f (weightedBound_of_supportedSeminorm s m (onModeSupport K f))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
