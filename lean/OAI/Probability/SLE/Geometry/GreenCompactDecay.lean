import OAI.Probability.SLE.Geometry.GreenMeanDecay
import OAI.Probability.SLE.Mass.LevelCurrentLimit
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

namespace OAI

/-! Spatially tested Green decay on interior compacts. This is the input
for exhaustion of the canonical terminal measure by finite times. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma halfPlaneGreenMeasure_mean_apply
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun s => B s ω)) (κ : ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (K : Set upperHalfPlane) (hK : MeasurableSet K) :
    P.bind (halfPlaneGreenMeasure κ B γ G t) K =
      ∫⁻ z in (Subtype.val : upperHalfPlane → ℂ) '' K,
        (∫⁻ ω, ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ * B s ω)
          (γ ω) (G ω) t z) ∂P) ∂volume := by
  have hL := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hK
  rw [Measure.bind_apply hK (halfPlaneGreenMeasure_measurable hBm hBc κ γ G F hw t).aemeasurable]
  have he (ω : Ω) : halfPlaneGreenMeasure κ B γ G t ω K =
      ∫⁻ z in (Subtype.val : upperHalfPlane → ℂ) '' K,
        ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ * B s ω)
          (γ ω) (G ω) t z) ∂volume := by
    rw [halfPlaneGreenMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
      withDensity_apply _ hL]
  simp_rw [he]
  exact lintegral_lintegral_swap
    ((actual_greenDensity_joint_measurable hBm hBc κ γ G F hw t).ennreal_ofReal.aemeasurable)

theorem halfPlaneGreenMeasure_compact_mean_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun s => B s ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    Tendsto (fun n : ℕ => P.bind (halfPlaneGreenMeasure κ B γ G n) K) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  let L := (Subtype.val : upperHalfPlane → ℂ) '' K
  have hL : IsCompact L := hK.image continuous_subtype_val
  have hLH : L ⊆ upperHalfPlane := by rintro _ ⟨z,_,rfl⟩; exact z.property
  have hfin : (∫⁻ z in L, ENNReal.ofReal (initialGreen κ z) ∂volume) ≠ ∞ := by
    have h := hK.measure_lt_top (μ := initialGreenMeasure κ)
    rw [initialGreenMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
      withDensity_apply _ hL.measurableSet] at h
    exact h.ne
  have hm (n : ℕ) : Measurable (fun z => ∫⁻ ω, ENNReal.ofReal
      (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) n z) ∂P) :=
    (actual_greenDensity_joint_measurable hBm hBc κ γ G F hw n).ennreal_ofReal.lintegral_prod_left
  have hb (n : ℕ) : (fun z => ∫⁻ ω, ENNReal.ofReal
      (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) n z) ∂P)
      ≤ᵐ[volume.restrict L] (fun z => ENNReal.ofReal (initialGreen κ z)) := by
    filter_upwards [ae_restrict_mem hL.measurableSet] with z hz
    exact greenDensity_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw z (hLH hz) n
  have hl : ∀ᵐ z ∂volume.restrict L, Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal
      (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) n z) ∂P) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem hL.measurableSet] with z hz
    exact (greenDensity_mean_tendsto_zero hB hBm hBc hB0 hκ hκ8 γ G F hw z (hLH hz)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ≥0)) atTop atTop)
  have hlim := tendsto_lintegral_of_dominated_convergence _ hm hb hfin hl
  simp only [lintegral_zero] at hlim
  simpa only [halfPlaneGreenMeasure_mean_apply P hBm hBc κ γ G F hw _ K hK.measurableSet] using hlim

end SLEExactGauge.Multipoint

end

end OAI
