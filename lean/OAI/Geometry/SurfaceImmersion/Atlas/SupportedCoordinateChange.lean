import OAI.Geometry.SurfaceImmersion.Atlas.SupportedWeightedSeminorm

namespace OAI

/-! Isometric linear coordinate changes preserve the supported weighted
seminorms exactly. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A B F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma weightedBound_comp_isometry (e : A ≃ₗᵢ[ℝ] B) {f : B → F}
    (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hb : WeightedBound Set.univ s m C f) :
    WeightedBound Set.univ s m C (f ∘ e) := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  change s ^ j * ‖iteratedFDeriv ℝ j
    (f ∘ (e.toContinuousLinearEquiv.toContinuousLinearMap : A → B)) x‖ ≤ C
  rw [e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x (by simp),
    ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]
  change s ^ j * ‖iteratedFDeriv ℝ j f (e x)‖ ≤ C
  simpa only [iteratedFDerivWithin_univ] using hb j hj (e x) (Set.mem_univ _)

def pushSupported (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A) (f : SupportedField (F := F) K) :
    SupportedField (F := F) (K.map e e.continuous) :=
  ⟨f ∘ e.symm, f.contDiff.comp e.symm.contDiff, fun y hy => by
    apply f.zero_on_compl
    intro hx
    exact hy ⟨e.symm y, hx, e.apply_symm_apply y⟩⟩

def pullSupported (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A)
    (f : SupportedField (F := F) (K.map e e.continuous)) : SupportedField (F := F) K :=
  ⟨f ∘ e, f.contDiff.comp e.contDiff, fun x hx => by
    apply f.zero_on_compl
    rintro ⟨z, hz, hzx⟩
    exact hx (e.injective hzx ▸ hz)⟩

def supportedCoordinateEquiv (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A) :
    SupportedField (F := F) K ≃ₗ[ℝ] SupportedField (F := F) (K.map e e.continuous) where
  toFun := pushSupported e K
  invFun := pullSupported e K
  left_inv f := by
    apply DFunLike.ext
    intro x
    change f (e.symm (e x)) = f x
    rw [e.symm_apply_apply]
  right_inv f := by
    apply DFunLike.ext
    intro x
    change f (e (e.symm x)) = f x
    rw [e.apply_symm_apply]
  map_add' f g := by
    apply DFunLike.ext
    intro x
    rfl
  map_smul' c f := by
    apply DFunLike.ext
    intro x
    rfl

lemma supportedCoordinateEquiv_norm (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A)
    {s : ℝ≥0} (hs : 0 < (s : ℝ)) (m : ℕ) (f : SupportedField (F := F) K) :
    supportedWeightedSeminorm (K.map e e.continuous) s m (supportedCoordinateEquiv e K f) =
      supportedWeightedSeminorm K s m f := by
  apply le_antisymm
  · apply supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _)
    exact weightedBound_comp_isometry e.symm f.contDiff (weightedBound_of_supportedSeminorm s m f)
  · have hb := weightedBound_comp_isometry e (supportedCoordinateEquiv e K f).contDiff
      (weightedBound_of_supportedSeminorm s m (supportedCoordinateEquiv e K f))
    have hid : (supportedCoordinateEquiv e K f : B → F) ∘ e = (f : A → F) := by
      funext x
      change f (e.symm (e x)) = f x
      rw [e.symm_apply_apply]
    rw [hid] at hb
    exact supportedSeminorm_le_of_weightedBound hs (apply_nonneg _ _) f hb

/-- The two coordinate conventions used by the geometric and jet formulas. -/
def planeCoordinateIsometry : (Fin 2 → ℝ) ≃ₗᵢ[ℝ] ℝ × ℝ where
  toLinearEquiv := LinearEquiv.finTwoArrow ℝ ℝ
  norm_map' x := by
    change max ‖x 0‖ ‖x 1‖ = ‖x‖
    apply le_antisymm
    · exact max_le (norm_le_pi_norm x 0) (norm_le_pi_norm x 1)
    · apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2
      intro i
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _

end ClosedSurfaceR4.JetPolynomial

end

end OAI
