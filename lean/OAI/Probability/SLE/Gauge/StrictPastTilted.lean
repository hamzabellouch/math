import OAI.Probability.SLE.Geometry.FinitePastKernel
import OAI.Probability.SLE.Gauge.StrictPastSpatial

namespace OAI

/-! The strict past-mass formula expressed through finite centered laws.
Every spatial integrand is identified before applying monotone convergence. -/

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

lemma finiteCenteredLaw_tests_spatial_tendsto
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    (hE : ∀ t∈I, MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] (E t))
    (K : Set ℂ) (hK : MeasurableSet K) (hKH : K ⊆ upperHalfPlane) :
    Tendsto (fun n => ∫⁻ z in K, ENNReal.ofReal (initialGreen κ z) *
      finiteCenteredLaw P κ B γ G z (u n)
        (finiteStrictPastEvent I E (fun ω => radiusLevelTime (γ ω) (G ω) z (u n))) ∂volume) atTop
      (𝓝 (∫⁻ z in K, ∑ t∈I, ∫⁻ ω in firstPastSuccess I E t,
        ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z) ∂P ∂volume)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hlevel (n : ℕ) :
      (∫⁻ z in K, ENNReal.ofReal (initialGreen κ z) * finiteCenteredLaw P κ B γ G z (u n)
        (finiteStrictPastEvent I E (fun ω => radiusLevelTime (γ ω) (G ω) z (u n))) ∂volume) =
      ∑ t∈I, ∫⁻ z in K, ∫⁻ ω in firstPastSuccess I E t,
        ENNReal.ofReal (levelCurrentGreen κ B γ G (u n) t z ω) ∂P ∂volume := by
    calc
      _ = ∫⁻ z in K, ∑ t∈I, ∫⁻ ω in firstPastSuccess I E t,
          ENNReal.ofReal (levelCurrentGreen κ B γ G (u n) t z ω) ∂P ∂volume := by
        apply setLIntegral_congr_fun hK
        intro z hz
        exact finiteCenteredLaw_tests hB hBm hc h0 hκ hκ8 γ G F hw z (hKH hz)
          (u n) (hu n) I E hE
      _ = _ := by
        apply lintegral_finsetSum
        intro t _
        exact (levelCurrentGreen_joint_measurable hBm hc κ (u n) (hu n) γ G F hw t).ennreal_ofReal.lintegral_prod_left'
  have hlast :
      (∫⁻ z in K, ∑ t∈I, ∫⁻ ω in firstPastSuccess I E t,
        ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z) ∂P ∂volume) =
      ∑ t∈I, ∫⁻ z in K, ∫⁻ ω in firstPastSuccess I E t,
        ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z) ∂P ∂volume := by
    apply lintegral_finsetSum
    intro t _
    exact (actual_greenDensity_joint_measurable hBm hc κ γ G F hw t).ennreal_ofReal.lintegral_prod_left'
  rw [hlast]
  simp_rw [hlevel]
  apply tendsto_finsetSum
  intro t _
  have hh := currentGreen_spatial_mean_tendsto P hBm hc κ γ G F hw u hu hmono hlim
    t K (fun _ => 1) measurable_const (firstPastSuccess I E t)
  have hs (n : ℕ) :
      (∫⁻ z in K, ∫⁻ ω in firstPastSuccess I E t,
        ENNReal.ofReal (levelCurrentGreen κ B γ G (u n) t z ω) ∂P ∂volume) =
      ∫⁻ ω in firstPastSuccess I E t, ∫⁻ z in K,
        ENNReal.ofReal (levelCurrentGreen κ B γ G (u n) t z ω) ∂volume ∂P :=
    (lintegral_lintegral_swap
      (levelCurrentGreen_joint_measurable hBm hc κ (u n) (hu n) γ G F hw t).ennreal_ofReal.aemeasurable).symm
  have hs' :
      (∫⁻ z in K, ∫⁻ ω in firstPastSuccess I E t,
        ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z) ∂P ∂volume) =
      ∫⁻ ω in firstPastSuccess I E t, ∫⁻ z in K,
        ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z) ∂volume ∂P :=
    (lintegral_lintegral_swap
      (actual_greenDensity_joint_measurable hBm hc κ γ G F hw t).ennreal_ofReal.aemeasurable).symm
  simpa only [one_mul, hs, hs'] using hh

namespace CanonicalMass

lemma finite_strict_past_tilted_limit
    (C : CanonicalMass P κ B hBm γ G)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    (hE : ∀ t∈I, MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] (E t))
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    Tendsto (fun n => ∫⁻ z in (Subtype.val : upperHalfPlane → ℂ) '' K,
      ENNReal.ofReal (initialGreen κ z) * finiteCenteredLaw P κ B γ G z (u n)
        (finiteStrictPastEvent I E (fun ω => radiusLevelTime (γ ω) (G ω) z (u n))) ∂volume) atTop
      (𝓝 (∫⁻ ω, C.rational.terminal ω (K ∩ ⋃ t∈I,
        if ω∈E t then {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t}ᶜ else ∅) ∂P)) := by
  rw [C.finite_strict_past_spatial hB hc h0 hκ hκ8 F hw I E hE K hK]
  apply finiteCenteredLaw_tests_spatial_tendsto hB hBm hc h0 hκ hκ8 γ G F hw u hu hmono hlim I E hE
    _ (hK.image continuous_subtype_val).measurableSet
  rintro _ ⟨z,_,rfl⟩
  exact z.property

end CanonicalMass
end SLEExactGauge.Multipoint

end

end OAI
