import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLE.Geometry.RestartContinuationKernel

namespace OAI

/-! The prescribed based-driver concatenation is the ordinary Brownian
continuation kernel, including its finite real-valued conditional mean. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

local instance targetContinuationPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance targetContinuationPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

def centerDriver (p : C(ℝ≥0, ℝ)) : Driver where
  toFun t := p t - p 0
  continuous_toFun := p.continuous.sub continuous_const
  map_zero' := sub_self _

lemma measurable_centerDriver : Measurable centerDriver := by
  apply ContinuousMapZero.isClosedEmbedding_toContinuousMap.measurableEmbedding.measurable_comp_iff.mp
  apply source_path_measurable
  intro t
  exact (continuous_eval_const t).measurable.sub (continuous_eval_const 0).measurable

lemma measurable_driverInclusion :
    Measurable (fun b : Driver => b.toContinuousMap) :=
  ContinuousMapZero.isClosedEmbedding_toContinuousMap.continuous.measurable

@[simp] lemma centerDriver_inclusion (b : Driver) : centerDriver b.toContinuousMap = b := by
  ext t
  change b t - b 0 = b t
  simp

lemma measurable_concat :
    Measurable (fun x : ℝ × (Driver × Driver) => concat x.2.1 x.2.2 x.1) := by
  apply ContinuousMapZero.isClosedEmbedding_toContinuousMap.measurableEmbedding.measurable_comp_iff.mp
  apply source_path_measurable
  intro u
  have ht : Measurable (fun x : ℝ × (Driver × Driver) => x.1.toNNReal) :=
    continuous_real_toNNReal.measurable.comp measurable_fst
  have hb : Measurable (fun x : ℝ × (Driver × Driver) => x.2.1 u) :=
    (continuous_eval_const u).measurable.comp (measurable_fst.comp measurable_snd)
  have hbt : Measurable (fun x : ℝ × (Driver × Driver) => x.2.1 x.1.toNNReal) :=
    continuous_eval.measurable.comp ((measurable_fst.comp measurable_snd).prodMk ht)
  have hc : Measurable (fun x : ℝ × (Driver × Driver) => x.2.2 (u-x.1.toNNReal)) :=
    continuous_eval.measurable.comp
      ((measurable_snd.comp measurable_snd).prodMk (measurable_const.sub ht))
  exact hb.ite (measurableSet_le measurable_const ht) (hbt.add hc)

lemma centerDriver_concatenate (b c : Driver) (t : ℝ≥0) :
    centerDriver (concatenateDriverPath t (driverPathStopped t b.toContinuousMap)
      c.toContinuousMap) = concat b c t := by
  ext u
  change (if u ≤ t then b (min u t) else b (min t t) + c (u-t) - c 0) -
    (if 0 ≤ t then b (min 0 t) else b (min t t) + c (0-t) - c 0) =
    (if u ≤ (t : ℝ).toNNReal then b u else b (t : ℝ).toNNReal + c (u-(t : ℝ).toNNReal))
  by_cases hu : u ≤ t
  · simp [hu]
  · simp [hu]

def driverFiltration : Filtration ℝ≥0 (borel Driver) :=
  Filtration.natural (fun t (b : Driver) => b t)
    (fun t => (continuous_eval_const t).measurable.stronglyMeasurable)

def continuationMean (W : WienerLaw) (t : ℝ) (f : Driver → ℝ≥0∞)
    (b : Driver) : ℝ≥0∞ := ∫⁻ c, f (concat b c t) ∂W

lemma measurable_continuationMean (W : WienerLaw) [SFinite W]
    (t : ℝ) (f : Driver → ℝ≥0∞) (hf : Measurable f) :
    Measurable (continuationMean W t f) := by
  exact (hf.comp (measurable_concat.comp
    (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))).lintegral_prod_right'

lemma continuationMean_eq_pathMean (W : WienerLaw) (t : ℝ≥0)
    (f : Driver → ℝ≥0∞) (hf : Measurable f) (b : Driver) :
    driverContinuationMean (W.map (fun c : Driver => c.toContinuousMap)) t
      (fun p => f (centerDriver p)) b.toContinuousMap = continuationMean W t f b := by
  have hm : Measurable (fun q : C(ℝ≥0, ℝ) =>
      f (centerDriver (concatenateDriverPath t (driverPathStopped t b.toContinuousMap) q))) :=
    (hf.comp measurable_centerDriver).comp (measurable_concatenateDriverPath.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  unfold driverContinuationMean
  rw [lintegral_map hm measurable_driverInclusion]
  simp only [centerDriver_concatenate, continuationMean]

lemma continuationMean_measurable_past (W : WienerLaw) [IsProbabilityMeasure W]
    (t : ℝ≥0) (f : Driver → ℝ≥0∞) (hf : Measurable f) :
    Measurable[driverFiltration t] (continuationMean W t f) := by
  let ν := W.map (fun c : Driver => c.toContinuousMap)
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff measurable_driverInclusion.aemeasurable).mpr inferInstance
  have hpath : Measurable[driverFiltration t, driverPathFiltration t]
      (fun b : Driver => b.toContinuousMap) :=
    driverPath_measurable_past_of_adapted driverFiltration _
      (fun s => (Filtration.stronglyAdapted_natural
        (fun u => (show Measurable (fun b : Driver => b u) from
          (continuous_eval_const u).measurable).stronglyMeasurable) s).measurable) t
  have hh := (driverContinuationMean_measurable ν t (fun p => f (centerDriver p))
    (hf.comp measurable_centerDriver)).comp hpath
  have he : (fun b : Driver => driverContinuationMean ν t
      (fun p => f (centerDriver p)) b.toContinuousMap) = continuationMean W t f :=
    funext (fun b => continuationMean_eq_pathMean W t f hf b)
  change Measurable[driverFiltration t] (fun b : Driver => driverContinuationMean ν t
    (fun p => f (centerDriver p)) b.toContinuousMap) at hh
  rwa [he] at hh

theorem continuationMean_condLExp (W : WienerLaw) (hW : IsWiener W)
    (t : ℝ≥0) (f : Driver → ℝ≥0∞) (hf : Measurable f) :
    continuationMean W t f =ᵐ[W] W⁻[f | driverFiltration t] := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have h := source_driver_continuation_condLExp hW
    (fun s => (continuous_eval_const s).measurable)
    (fun b => map_continuous b) t (fun p => f (centerDriver p))
    (hf.comp measurable_centerDriver)
  change (fun b : Driver => driverContinuationMean
      (W.map (fun c : Driver => c.toContinuousMap)) t
      (fun p => f (centerDriver p)) b.toContinuousMap) =ᵐ[W]
    W⁻[(fun b : Driver => f (centerDriver b.toContinuousMap)) | driverFiltration t] at h
  have he : (fun b : Driver => driverContinuationMean
      (W.map (fun c : Driver => c.toContinuousMap)) t
      (fun p => f (centerDriver p)) b.toContinuousMap) = continuationMean W t f :=
    funext (fun b => continuationMean_eq_pathMean W t f hf b)
  rw [he] at h
  simpa only [centerDriver_inclusion] using h

theorem continuationMean_setLIntegral (W : WienerLaw) (hW : IsWiener W)
    (t : ℝ≥0) (f : Driver → ℝ≥0∞) (hf : Measurable f)
    (A : Set Driver) (hA : MeasurableSet[driverFiltration t] A) :
    (∫⁻ b in A, continuationMean W t f b ∂W) = ∫⁻ b in A, f b ∂W := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  rw [lintegral_congr_ae (ae_restrict_of_ae (continuationMean_condLExp W hW t f hf))]
  exact setLIntegral_condLExp (driverFiltration.le t) W f hA

theorem continuationMean_finite_condExp (W : WienerLaw) (hW : IsWiener W)
    (t : ℝ≥0) (f : Driver → ℝ≥0∞) (hf : Measurable f)
    (hfin : (∫⁻ b, f b ∂W) ≠ ∞) :
    (∀ᵐ b ∂W, continuationMean W t f b < ∞) ∧
    (fun b => (continuationMean W t f b).toReal) =ᵐ[W]
      W[fun b => (f b).toReal | driverFiltration t] := by
  have he := continuationMean_condLExp W hW t f hf
  constructor
  · filter_upwards [he, condLExp_lt_top (mΩ := driverFiltration t) hfin] with b hb hbfin
    exact hb.symm ▸ hbfin
  · exact (he.fun_comp ENNReal.toReal).trans (toReal_condLExp _ hf.aemeasurable hfin)

end SLEExactGauge.Target

end

end OAI
