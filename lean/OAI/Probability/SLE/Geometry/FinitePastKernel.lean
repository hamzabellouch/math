import OAI.Probability.SLE.Geometry.FiniteCenteredPast
import OAI.Probability.SLE.Geometry.FinitePastEvents

namespace OAI

/-! Finite strict past events under a single finite centered law. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
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

lemma finiteCenteredLaw_tests (z : ℂ) (hz : z ∈ upperHalfPlane)
    (u : ℝ) (hu : 0 ≤ u) (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    (hE : ∀ t∈I, MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] (E t)) :
    ENNReal.ofReal (initialGreen κ z) * finiteCenteredLaw P κ B γ G z u
      (finiteStrictPastEvent I E (fun ω => radiusLevelTime (γ ω) (G ω) z u)) =
      ∑ t∈I, ∫⁻ ω in firstPastSuccess I E t,
        ENNReal.ofReal (levelCurrentGreen κ B γ G u t z ω) ∂P := by
  let ℱ := Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hp : Measurable (fun ω : Ω => (ω,z)) := measurable_id.prodMk measurable_const
  have hj := (actual_radiusLevel_joint_measurable hm hc κ u hu γ G F hw).comp hp
  have hT : Measurable (fun ω => radiusLevelTime (γ ω) (G ω) z u) := by
    simpa only [Function.comp_def] using hj
  rw [finiteStrictPastEvent_measure _ ℱ I E hE _ hT, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact finiteCenteredLaw_strict_past hB hBm hc h0 hκ hκ8 γ G F hw z hz u hu t _
    (firstPastSuccess_measurable ℱ I E hE ht)

lemma finiteCenteredLaw_tests_tendsto (z : ℂ) (hz : z ∈ upperHalfPlane)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    (hE : ∀ t∈I, MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] (E t)) :
    Tendsto (fun n => ENNReal.ofReal (initialGreen κ z) *
      finiteCenteredLaw P κ B γ G z (u n)
        (finiteStrictPastEvent I E (fun ω => radiusLevelTime (γ ω) (G ω) z (u n)))) atTop
      (𝓝 (∑ t∈I, ∫⁻ ω in firstPastSuccess I E t,
        ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z) ∂P)) := by
  let ℱ := Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)
  have h := tendsto_finsetSum I (fun t ht =>
    finiteCenteredLaw_strict_past_tendsto hB hBm hc h0 hκ hκ8 γ G F hw z hz u hu hmono hlim t
      (firstPastSuccess I E t) (firstPastSuccess_measurable ℱ I E hE ht))
  simp only [← Finset.mul_sum] at h
  apply h.congr'
  filter_upwards [] with n
  rw [finiteStrictPastEvent_measure _ ℱ I E hE]
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hp : Measurable (fun ω : Ω => (ω,z)) := measurable_id.prodMk measurable_const
  have hj := (actual_radiusLevel_joint_measurable hm hc κ (u n) (hu n) γ G F hw).comp hp
  simpa only [Function.comp_def] using hj

end SLEExactGauge.Multipoint

end

end OAI
