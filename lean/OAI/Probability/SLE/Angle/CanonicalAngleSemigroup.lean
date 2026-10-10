import OAI.Probability.SLE.Angle.RadiusAngleBounds

namespace OAI

/-! Probability and composition of the actual finite centered angle
transition, before its quantitative convergence is estimated. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance angleSemigroupMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance angleSemigroupBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
  (hB : IsBrownianReal B P) (hBm : Measurable (Function.uncurry B))
  (hc : ∀ ω, Continuous (fun t => B t ω))
  (hκ : 0<κ) (hκ8 : κ<8)
  (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))

include hB hBm hc hκ hκ8 γ G F hw

lemma canonicalAngleAverage_eq_finiteCentered
    (u : ℝ) (hu : 0≤u) (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ u f θ =
      ∫⁻ ω, f (extendedMarkedAngle κ B γ G
        (fun ω => radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) u)
        (Target.diskMapInv θ 0) ω) ∂finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) u := by
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  have hz := Target.diskMapInv_maps hθ (show (0:ℂ)∈ball 0 1 by simp)
  have hfm : Measurable (fun p : C(ℝ≥0,ℝ) =>
      f (canonicalStoppedAngle κ (u,Target.diskMapInv θ 0,p))) :=
    hf.comp ((canonicalStoppedAngle_measurable κ).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  unfold canonicalAngleAverage
  rw [← canonical_finiteCenteredLaw_map P κ B hm hc γ G F (Eventually.of_forall hw) u hu,
    lintegral_map' hfm.aemeasurable (source_path_measurable _ hm).aemeasurable]
  have ht := finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F
    (Eventually.of_forall hw) (Target.diskMapInv θ 0) hz u u hu le_rfl
    (fun ω => radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) u)
    (Eventually.of_forall fun _ => le_rfl)
  apply lintegral_congr_ae
  filter_upwards [ht] with ω hω
  have hfin : radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) u<∞ :=
    lt_top_iff_ne_top.mpr hω
  rw [canonicalStoppedAngle_eq κ (sourceDriverPath B hc ω) (hw ω) u hu _ hfin,
    extendedMarkedAngle_at_finite_radius κ B hc γ G F hw _ u ω hfin]
  rfl

lemma canonicalAngleAverage_one
    (u : ℝ) (hu : 0≤u) (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) :
    canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ u (fun _ => 1) θ=1 := by
  rw [canonicalAngleAverage_eq_finiteCentered hB hBm hc hκ hκ8 γ G F hw u hu θ hθ
    (fun _ => 1) measurable_const]
  let := finiteCenteredLaw_probability hB κ hκ hκ8 γ G F (Eventually.of_forall hw)
    (Target.diskMapInv θ 0) (Target.diskMapInv_maps hθ (by simp)) u hu
  simp

lemma canonicalAngleAverage_comp
    (h0 : ∀ ω, B 0 ω=0)
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (u v : ℝ) (hu : 0≤u) (hv : 0<v)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ (u+v) f θ =
      canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ u
        (canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ v f) θ := by
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let ν := P.map (sourceDriverPath B hc)
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (source_path_measurable _ hm).aemeasurable).mpr inferInstance
  let z := Target.diskMapInv θ 0
  have hz : z∈upperHalfPlane := Target.diskMapInv_maps hθ (by simp)
  let ℱ := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let S : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z u
  have hS : IsStoppingTime ℱ S :=
    actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz u hu
  let g : Ω → ℝ≥0∞ := fun ω => canonicalAngleAverage ν κ v f
    (extendedMarkedAngle κ B γ G S z ω)
  have hfm : Measurable (canonicalAngleAverage ν κ v f) :=
    canonicalAngleAverage_measurable ν κ v f hf
  have hgm : Measurable[hS.measurableSpace] g := hfm.comp
    (extendedMarkedAngle_measurable B hm hc κ γ G F hw S hS z)
  rw [canonicalAngleAverage_eq_finiteCentered hB hBm hc hκ hκ8 γ G F hw
    (u+v) (by linarith) θ hθ f hf,
    canonicalAngleAverage_eq_finiteCentered hB hBm hc hκ hκ8 γ G F hw u hu θ hθ _ hfm]
  have hk := radius_angle_kernel hB hBm hc h0 hκ hκ8 γ G F hw hpublished
    z hz u v (u+v) hu hv le_rfl f hf univ MeasurableSet.univ
  simp only [setLIntegral_univ] at hk
  rw [← hk]
  exact @lintegral_eq_of_stopped_events Ω mΩ
    (finiteCenteredLaw P κ B γ G z (u+v)) (finiteCenteredLaw P κ B γ G z u)
    hS.measurableSpace hS.measurableSpace_le
    (fun E hE => finiteCenteredLaw_consistent_at_extended_stop hB hBm hc h0 κ hκ hκ8
      γ G F (Eventually.of_forall hw) z hz u (u+v) hu (by linarith) S hS
      (Eventually.of_forall fun _ => le_rfl) E hE) g hgm

end SLEExactGauge

end

end OAI
