import OAI.Probability.SLE.Mass.CanonicalImageMass
import OAI.Probability.SLE.Loewner.StoppedInversePaths

namespace OAI

/-! Fixed conformal changes of coordinates preserve restart increments.
Composition combines the two density weights before pushing forward. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge

local instance conformalRestartLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

lemma weightedImageMass_comp
    {X : Type*} [MeasurableSpace X]
    (J : upperHalfPlane → X) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) (hw : Measurable w)
    (F : upperHalfPlane → upperHalfPlane) (hF : Measurable F)
    (v : upperHalfPlane → ℝ≥0∞) (hv : Measurable v)
    (η : Measure upperHalfPlane) :
    weightedImageMass J w (weightedImageMass F v η) =
      weightedImageMass (J ∘ F) (fun z => v z*w (F z)) η := by
  classical
  apply Measure.ext
  intro A hA
  rw [weightedImageMass_apply J hJ w _ A hA,
    weightedImageMass_lintegral F hF v hv η ((J ⁻¹' A).indicator w)
      (hw.indicator (hJ hA)),
    weightedImageMass_apply (J ∘ F) (hJ.comp hF) _ η A hA]
  apply lintegral_congr
  intro z
  change v z * (if J (F z) ∈ A then w (F z) else 0) =
    (if J (F z) ∈ A then v z*w (F z) else 0)
  split_ifs <;> simp

lemma derivative_dimension_weight_comp
    (κ : ℝ) (J F : ℂ → ℂ) (z : ℂ)
    (hJ : DifferentiableAt ℂ J (F z)) (hF : DifferentiableAt ℂ F z) :
    ENNReal.ofReal (‖deriv F z‖ ^ dimension κ) *
        ENNReal.ofReal (‖deriv J (F z)‖ ^ dimension κ) =
      ENNReal.ofReal (‖deriv (J ∘ F) z‖ ^ dimension κ) := by
  rw [deriv_comp z hJ hF,norm_mul,Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
  exact mul_comm _ _

namespace Multipoint

variable {D : Set ℂ}

lemma conformalMass_sub
    (J : upperHalfPlane ≃ₜ D) (w : C(upperHalfPlane,ℝ≥0))
    {μ ν : Measure upperHalfPlane} [IsFiniteMeasureOnCompacts ν] (hle : μ ≤ ν) :
    conformalMass J w (ν-μ) = conformalMass J w ν-conformalMass J w μ := by
  let : IsFiniteMeasureOnCompacts μ :=
    ⟨fun K hK => lt_of_le_of_lt (hle K) hK.measure_lt_top⟩
  let : IsLocallyFiniteMeasure (μ.withDensity (fun z => (w z : ℝ≥0∞))) :=
    IsLocallyFiniteMeasure.withDensity_coe w.continuous
  let : SigmaFinite (conformalMass J w μ) := J.measurableEmbedding.sigmaFinite_map
  apply (Measure.add_left_inj (conformalMass J w μ) _ _).mp
  calc
    conformalMass J w (ν-μ)+conformalMass J w μ = conformalMass J w ν := by
      rw [← conformalMass_add,sigmaFinite_sub_add_cancel_of_le hle]
    _ = (conformalMass J w ν-conformalMass J w μ)+conformalMass J w μ :=
      (sigmaFinite_sub_add_cancel_of_le (conformalMass_mono J w hle)).symm

lemma conformalMass_weightedImageMass
    (J : upperHalfPlane ≃ₜ D) (w : C(upperHalfPlane,ℝ≥0))
    (F : upperHalfPlane → upperHalfPlane) (hF : Measurable F)
    (v : upperHalfPlane → ℝ≥0∞) (hv : Measurable v) (η : Measure upperHalfPlane) :
    conformalMass J w (weightedImageMass F v η) =
      weightedImageMass (J ∘ F) (fun z => v z*(w (F z) : ℝ≥0∞)) η :=
  weightedImageMass_comp J J.continuous.measurable _
    w.continuous.measurable.coe_nnreal_ennreal F hF v hv η

lemma conformalMass_increment_of_restart
    (J : upperHalfPlane ≃ₜ D) (w : C(upperHalfPlane,ℝ≥0))
    {μ ν : Measure upperHalfPlane} [IsFiniteMeasureOnCompacts ν] (hle : μ ≤ ν)
    (F : upperHalfPlane → upperHalfPlane) (hF : Measurable F)
    (v : upperHalfPlane → ℝ≥0∞) (hv : Measurable v) (η : Measure upperHalfPlane)
    (hrestart : ν-μ = weightedImageMass F v η) :
    conformalMass J w ν-conformalMass J w μ =
      weightedImageMass (J ∘ F) (fun z => v z*(w (F z) : ℝ≥0∞)) η := by
  rw [← conformalMass_sub J w hle,hrestart]
  exact conformalMass_weightedImageMass J w F hF v hv η

end Multipoint
end SLEExactGauge

end

end OAI
