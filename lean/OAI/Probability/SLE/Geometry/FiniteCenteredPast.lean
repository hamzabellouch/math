import OAI.Probability.SLE.Mass.LevelCurrentLimit
import OAI.Probability.SLE.Gauge.CoverChangeOfLaw

namespace OAI

/-! Strict past tests of the finite centered laws and their increasing-level limit.
The event remains strictly before the marked radius level. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge.Multipoint

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
  (hB : IsBrownianReal B P) (hBm : Measurable (Function.uncurry B))
  (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω = 0)
  (hκ : 0 < κ) (hκ8 : κ < 8)
  (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))

include hB hBm hc h0 hκ hκ8 γ G F hw

lemma finiteCenteredLaw_strict_past (z : ℂ) (hz : z ∈ upperHalfPlane)
    (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] E) :
    ENNReal.ofReal (initialGreen κ z) * finiteCenteredLaw P κ B γ G z u
      (E ∩ {ω | (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u}) =
      ∫⁻ ω in E, ENNReal.ofReal (levelCurrentGreen κ B γ G u t z ω) ∂P := by
  let ℱ := Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)
  let A : Set Ω := {ω | (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u}
  have hA : MeasurableSet A := by
    have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
    have hj := actual_radiusLevel_joint_measurable hm hc κ u hu γ G F hw
    have hp : Measurable (fun ω : Ω => (ω,z)) := measurable_id.prodMk measurable_const
    have htt := hj.comp hp
    have ht : Measurable (fun ω => radiusLevelTime (γ ω) (G ω) z u) := by
      simpa only [Function.comp_def] using htt
    exact measurableSet_lt (measurable_const : Measurable (fun _ : Ω => (t : ℝ≥0∞))) ht
  have hEg : MeasurableSet E := (ℱ.le t) _ hE
  calc
    _ = ∫⁻ ω in E ∩ A, ENNReal.ofReal
        (stoppedGreen κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) z u) ∂P :=
      (finiteCenteredLaw_event_identity P κ B γ G z hz u (hEg.inter hA)).symm
    _ = ∫⁻ ω in E, ENNReal.ofReal (levelRemainderGreen κ B γ G u t z ω) ∂P := by
      rw [inter_comm E A, ← setLIntegral_indicator hA]
      apply lintegral_congr
      intro ω
      by_cases ha : ω ∈ A
      · have hh : (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u := ha
        rw [indicator_of_mem ha, levelRemainderGreen, ite_eq_left hh]
      · have hh : ¬ (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u := ha
        rw [indicator_of_notMem ha, levelRemainderGreen, ite_eq_right hh, ENNReal.ofReal_zero]
    _ = _ := levelRemainderGreen_setLIntegral hB hBm hc h0 hκ hκ8 γ G F
      (ae_of_all _ hw) z hz u hu t E hE

lemma finiteCenteredLaw_strict_past_tendsto
    (z : ℂ) (hz : z ∈ upperHalfPlane)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (t : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] E) :
    Tendsto (fun n => ENNReal.ofReal (initialGreen κ z) *
      finiteCenteredLaw P κ B γ G z (u n)
        (E ∩ {ω | (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z (u n)})) atTop
      (𝓝 (∫⁻ ω in E, ENNReal.ofReal
        (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z) ∂P)) := by
  simp_rw [finiteCenteredLaw_strict_past hB hBm hc h0 hκ hκ8 γ G F hw z hz _ (hu _) t E hE]
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    have hp : Measurable (fun ω : Ω => (ω,z)) := measurable_id.prodMk measurable_const
    have hh := (levelCurrentGreen_joint_measurable hBm hc κ (u n) (hu n) γ G F hw t).comp hp
    have hh' : Measurable (fun ω => levelCurrentGreen κ B γ G (u n) t z ω) := by
      simpa only [Function.comp_def] using hh
    exact hh'.ennreal_ofReal.aemeasurable
  · exact ae_of_all _ (fun ω n m hnm => ENNReal.ofReal_le_ofReal
      (levelCurrentGreen_mono ω (hc ω) (hw ω) z t (hu n) (hmono hnm)))
  · exact ae_of_all _ (fun ω => tendsto_const_nhds.congr'
      ((levelCurrentGreen_eventually_eq ω (hc ω) (hw ω) z t u hu hlim).mono
        (fun n hn => congrArg ENNReal.ofReal hn.symm)))

end SLEExactGauge.Multipoint

end

end OAI
