import OAI.Probability.SLE.Gauge.SerpentineExponentialMass
import OAI.Probability.SLE.Gauge.RibbonStoppedMassLaw

namespace OAI

/-! The stopped dense serpentine experiment in the original half-plane
coordinates, with one common physical sausage mesh and its exact m^(2-d)
mass threshold. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates Target ScaleTraceLaw RibbonPassageScaling

local instance : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma physicalExperimentChart_closedEmbedding {s : ℝ} (hs : 0 < s) (w : ℂ)
    (hw : s ≤ w.im) {m : ℕ} (hm : 0 < m) :
    Topology.IsClosedEmbedding (fun z : closedRibbon => physicalExperimentChart s w m z) := by
  have hℓ := fit_width_pos hs hm
  have hh := (Homeomorph.mulLeft₀ (ribbonWidth (halfHeight s) m : ℂ)
    (Complex.ofReal_ne_zero.mpr hℓ.ne')).isClosedEmbedding.comp
    (experimentChart_closedEmbedding hs w hw hm)
  change Topology.IsClosedEmbedding (fun z : closedRibbon =>
    (ribbonWidth (halfHeight s) m : ℂ) * experimentChart s w m z) at hh
  simpa only [Function.comp_def, physicalExperimentChart_eq] using hh

lemma normalizedExperimentDisk_scaled {s : ℝ} (hs : 0 < s) (w : ℂ)
    {m : ℕ} (hm : 0 < m) :
    affine 0 (ribbonWidth (halfHeight s) m) '' normalizedExperimentDisk s w m =
      closedBall (center s w) (s / 20) := by
  have hℓ := fit_width_pos hs hm
  change (fun z : ℂ => 0 + (ribbonWidth (halfHeight s) m : ℂ) * z) ''
    ((fun z : ℂ => (ribbonWidth (halfHeight s) m : ℂ) * z) ⁻¹' closedBall (center s w) (s / 20)) = _
  have hh := Set.image_preimage_eq (closedBall (center s w) (s / 20)) (affine_bijective 0 hℓ).surjective
  change (fun z : ℂ => 0 + (ribbonWidth (halfHeight s) m : ℂ) * z) ''
    ((fun z : ℂ => 0 + (ribbonWidth (halfHeight s) m : ℂ) * z) ⁻¹'
      closedBall (center s w) (s / 20)) = _ at hh
  simpa only [zero_add] using hh

lemma physical_ribbon_mass_threshold (κ c s : ℝ) (hs : 0 < s)
    (m : ℕ) (hm : 0 < m) :
    ENNReal.ofReal (ribbonWidth (halfHeight s) m ^ dimension κ) *
        (((m ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal c) =
      ENNReal.ofReal (c * (s / 20000) ^ dimension κ * (m : ℝ) ^ codimension κ) := by
  have he : ribbonWidth (halfHeight s) m = (s / 20000) / (m : ℝ) := by
    rw [fit_width_eq]
    rw [div_div]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (m ^ 2 : ℕ)),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (fit_width_pos hs hm).le _)]
  congr 1
  rw [he]
  simp only [Nat.cast_pow]
  exact ribbon_mass_after_width_scaling κ c (s / 20000) (by positivity) m hm

theorem uniform_serpentine_physical_stopped_mass
    {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport μ γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) :
    ∃ c v₀ : ℝ, 0 < c ∧ 0 < v₀ ∧ ∀ s : ℝ, 0 < s →
      ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → s ≤ w.im → ∀ m : ℕ, 0 < m →
      ∀ v : ℝ, 0 < v → v < ribbonWidth (halfHeight s) m * v₀ → ∀ g : C(ℂ, ℝ),
      (∀ z ∈ closedRibbon, g (physicalExperimentChart s w m z) = z.re) →
      ENNReal.ofReal (Real.exp (-C * (m : ℝ) ^ 2)) ≤ μ {ω |
        ω ∈ GoodRibbonPrefix γ (ribbonIntegerFront g γ (experimentSteps s w m))
          (physicalExperimentChart s w m) ε ∧
        ENNReal.ofReal (c * (s / 20000) ^ dimension κ * (m : ℝ) ^ codimension κ) ≤
          segmentSausageCharge κ (γ ω) 0
            ((ribbonIntegerFront g γ (experimentSteps s w m) ω).untopD 0)
            v (closedBall (center s w) (s / 20))} := by
  obtain ⟨c, v₀, hcm, hv₀, hprob⟩ := uniform_serpentine_exponential_stopped_mass μ κ hκ hκ8
    B hB hm hc γ G F hw hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW ε hε hεsmall
  let f := sourceTracePath γ (fun ω => (hw ω).1)
  have ha := brownian_capacity_trace_adapted B hm hc κ γ G F hw
  have hfm : Measurable f := source_path_measurable _
    (fun t => (ha t).mono (Filtration.le _ t) le_rfl)
  refine ⟨c, v₀, hcm, hv₀, fun s hs => ?_⟩
  obtain ⟨C, hC, hprob⟩ := hprob s hs
  refine ⟨C, hC, fun w hwn hwy m hmp v hv hvcut g hg => ?_⟩
  let ℓ := ribbonWidth (halfHeight s) m
  have hℓ : 0 < ℓ := fit_width_pos hs hmp
  let ell : ℝ≥0 := ⟨ℓ, hℓ.le⟩
  have hell : 0 < ell := hℓ
  let gn : C(ℂ, ℝ) := g.comp ⟨fun z : ℂ => (ℓ : ℂ) * z, continuous_const.mul continuous_id⟩
  have hgg (z : ℂ) : g ((ell : ℂ) * z) = gn z := rfl
  have hgn (z : ℂ) (hz : z ∈ closedRibbon) : gn (experimentChart s w m z) = z.re := by
    change g ((ℓ : ℂ) * experimentChart s w m z) = z.re
    rw [← physicalExperimentChart_eq]
    exact hg z hz
  have hvn : 0 < v / ℓ := div_pos hv hℓ
  have hvncut : v / ℓ < v₀ := (div_lt_iff₀ hℓ).mpr (by simpa only [mul_comm] using hvcut)
  have hstart := hprob (v / ℓ) hvn hvncut w hwn hwy m hmp gn hgn
  have he : Topology.IsClosedEmbedding (fun z : closedRibbon => (ell : ℂ) * experimentChart s w m z) := by
    have he' := physicalExperimentChart_closedEmbedding hs w hwy hmp
    simp only [physicalExperimentChart_eq] at he'
    change Topology.IsClosedEmbedding (fun z : closedRibbon =>
      (ribbonWidth (halfHeight s) m : ℂ) * experimentChart s w m z)
    exact he'
  have htrans := ribbonStoppedMass_scale_probability μ f hfm ell hell
    (scaled_trace_path_law κ hκ hκ8 B hB hm hc γ G F hw ell hell)
    (experimentChart s w m) he gn g hgg ((experimentSteps s w m : ℝ) + 1) ε κ hvn
    (normalizedExperimentDisk s w m) (((m ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal c)
  have hmass := physical_ribbon_mass_threshold κ c s hs m hmp
  have hmesh : (ell : ℝ) * (v / ℓ) = v := mul_div_cancel₀ v hℓ.ne'
  have hregion : affine 0 (ell : ℝ) '' normalizedExperimentDisk s w m =
      closedBall (center s w) (s / 20) := normalizedExperimentDisk_scaled hs w hmp
  apply hstart.trans
  have hchart : (fun z : ℂ => (ell : ℂ) * experimentChart s w m z) = physicalExperimentChart s w m := by
    funext z
    exact (physicalExperimentChart_eq s w m z).symm
  have hmass' : ENNReal.ofReal ((ell : ℝ) ^ dimension κ) *
      (((m ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal c) =
      ENNReal.ofReal (c * (s / 20000) ^ dimension κ * (m : ℝ) ^ codimension κ) := hmass
  simpa only [ribbonStoppedMassEvent, GoodRibbonPrefix, mem_ofPred_eq, f, sourceTracePath,
    ContinuousMap.coe_mk, ribbonIntegerFront, ribbonFrontStop, hmesh, hregion, hmass', hchart] using htrans

end SLEExactGauge.Serpentine

end

end OAI
