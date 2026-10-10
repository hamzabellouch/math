import OAI.Analysis.KadisonKastler.L2GaugeStarTransport
import OAI.Analysis.KadisonKastler.SpatialAssociatorTransport

namespace OAI

/-! # Pointwise spatial identifications on the regular Hilbert space -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def pointwiseL2Unitary (V : H ≃ₗᵢ[ℂ] K) :
    RegularCoreHilbert H ≃ₗᵢ[ℂ] RegularCoreHilbert K where
  toFun := V.toLinearIsometry.toContinuousLinearMap.compLp
  invFun := V.symm.toLinearIsometry.toContinuousLinearMap.compLp
  left_inv f := by
    apply Lp.ext
    filter_upwards [V.symm.toLinearIsometry.toContinuousLinearMap.coeFn_compLp (V.toLinearIsometry.toContinuousLinearMap.compLp f),
      V.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f] with t hs hv
    rw [hs, hv]
    exact V.symm_apply_apply (f t)
  right_inv f := by
    apply Lp.ext
    filter_upwards [V.toLinearIsometry.toContinuousLinearMap.coeFn_compLp (V.symm.toLinearIsometry.toContinuousLinearMap.compLp f),
      V.symm.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f] with t hv hs
    rw [hv, hs]
    exact V.apply_symm_apply (f t)
  map_add' := (V.toLinearIsometry.toContinuousLinearMap.compLpₗ 2 (volume : Measure ℝ)).map_add
  map_smul' := (V.toLinearIsometry.toContinuousLinearMap.compLpₗ 2 (volume : Measure ℝ)).map_smul
  norm_map' f := by
    have he : ∀ᵐ t ∂(volume : Measure ℝ),
        ‖V.toLinearIsometry.toContinuousLinearMap.compLp f t‖ = ‖f t‖ := by
      filter_upwards [V.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f] with t hv
      rw [hv]
      exact V.norm_map (f t)
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
      (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))

omit [CompleteSpace H] [CompleteSpace K] in
theorem pointwiseL2Unitary_apply_ae (V : H ≃ₗᵢ[ℂ] K) (f : RegularCoreHilbert H) :
    pointwiseL2Unitary V f =ᵐ[volume] fun t => V (f t) :=
  V.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f

theorem compLp_regularRightTranslation (L : H →L[ℂ] K)
    (s : Multiplicative ℝ) (f : RegularCoreHilbert H) :
    L.compLp ((regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
    (regularRightTranslation (H := K) s :
      RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K) (L.compLp f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp ((regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularRightTranslation_apply_ae s f,
    regularRightTranslation_apply_ae s (L.compLp f),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (L.coeFn_compLp f)] with t hl hs ht hf
  simp only [Function.comp_def] at hf
  rw [hl, hs, ht, hf]

theorem pointwiseL2Unitary_translation (V : H ≃ₗᵢ[ℂ] K) (s : Multiplicative ℝ) :
    (pointwiseL2Unitary V).conjStarAlgEquiv
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularRightTranslation (H := K) s :
        RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change V.toLinearIsometry.toContinuousLinearMap.compLp
      ((regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        ((pointwiseL2Unitary V).symm f)) = _
  rw [compLp_regularRightTranslation]
  change (regularRightTranslation (H := K) s :
    RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K)
    (pointwiseL2Unitary V ((pointwiseL2Unitary V).symm f)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

end

end KadisonKastler

end OAI
