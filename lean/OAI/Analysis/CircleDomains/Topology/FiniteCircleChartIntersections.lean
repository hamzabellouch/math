import OAI.Analysis.CircleDomains.Transfer.FiniteRealChartIntersections
import OAI.Analysis.CircleDomains.Sobolev.CircleBranchEnergy
import OAI.Analysis.CircleDomains.Selection.FiniteLevelAssembly

namespace OAI

/-! Two branch cuts cover a smooth circle coordinate. Each branch has
the intrinsic differential, so scalar coarea gives a finite expected
intersection count without a global real lift. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem mean_circle_chart_count_finite
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {D K : Set ℂ} (hD : IsOpen D) (hK : IsCompact K)
    (hAG : ∀ z ∈ K ∩ D, (z : Sphere) ∈ G)
    {f : ℂ → UnitAddCircle} (hf : SmoothCircleOn f D)
    (henergy : (∫⁻ z in D, ENNReal.ofReal ‖circleFDeriv f z‖ ^ 2) < ∞)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (hfinite : ∀ᵐ γ ∂(μ : Measure _), physicalDomainLength e y₀ γ < ∞)
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanPhysicalOccupation e y₀ μ = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (a b : ℝ) (hab : (a : UnitAddCircle) ≠ (b : UnitAddCircle)) :
    (∫⁻ θ : UnitAddCircle, ∫⁻ γ,
      pathImageCount ((fun z : ℂ => π (z : Sphere)) '' ((K ∩ D) ∩ {z | f z = θ}))
        γ ∂(μ : Measure _)) < ∞ := by
  let O (c : ℝ) := D ∩ f ⁻¹' ({(c : UnitAddCircle)}ᶜ)
  let A (c : ℝ) := K ∩ O c
  let S (c : ℝ) (θ : UnitAddCircle) := (fun z : ℂ => π (z : Sphere)) ''
    (A c ∩ {z | (circleBranch f c z : UnitAddCircle) = θ})
  have hO (c : ℝ) : IsOpen (O c) :=
    hf.continuousOn.isOpen_inter_preimage hD isClosed_singleton.isOpen_compl
  have hσ (c : ℝ) : IsSigmaCompact (A c) := by
    let : LocallyCompactSpace (O c) := (hO c).locallyCompactSpace
    have hs : IsSigmaCompact (O c) := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
    obtain ⟨Q, hQ, hcov⟩ := hs
    refine ⟨fun n => K ∩ Q n, fun n => (hQ n).inter_left hK.isClosed, ?_⟩
    rw [← inter_iUnion, hcov]
  have hcut (c : ℝ) : ∀ z ∈ O c, f z ≠ (c : UnitAddCircle) := fun _ hz => hz.2
  have hbranch (c : ℝ) := smooth_circleBranch hf c
    (show O c ⊆ D from inter_subset_left) (hcut c)
  have hmean (c : ℝ) : (∫⁻ θ : UnitAddCircle, ∫⁻ γ,
      pathImageCount (S c θ) γ ∂(μ : Measure _)) < ∞ :=
    mean_real_chart_circle_count_finite hcoarea e hU y₀ π hπ he (hσ c) hK
      inter_subset_left (fun z hz => hAG z ⟨hz.1, hz.2.1⟩) inter_subset_right (hO c)
      ((hbranch c).of_le (by norm_num))
      ((circleBranch_energy_le hf c (hO c).measurableSet inter_subset_left (hcut c) volume).trans_lt henergy)
      μ hfinite ρ hρ hocc hρ2
  have hmeas (c : ℝ) (θ : UnitAddCircle) : Measurable
      (fun γ : C(PathTime, Sphere) => pathImageCount (S c θ) γ) :=
    (measurable_sigmaCompact_chart_circle_count (fun z : ℂ => π (z : Sphere))
      (hπ.comp OnePoint.continuous_coe) (hσ c) (circleBranch f c)
      ((hbranch c).continuousOn.mono inter_subset_right)).comp
        (measurable_id.prodMk measurable_const)
  have hcover (θ : UnitAddCircle) (γ : C(PathTime, Sphere)) :
      pathImageCount ((fun z : ℂ => π (z : Sphere)) '' ((K ∩ D) ∩ {z | f z = θ})) γ ≤
        pathImageCount (S a θ) γ + pathImageCount (S b θ) γ := by
    apply pathImageCount_le_of_cover
    rintro x ⟨_, z, hz, rfl⟩
    by_cases hza : f z ≠ (a : UnitAddCircle)
    · exact Or.inl ⟨z, ⟨⟨hz.1.1, hz.1.2, hza⟩, by simpa only [coe_circleBranch] using hz.2⟩, rfl⟩
    · have hzb : f z ≠ (b : UnitAddCircle) := fun h => hab ((not_not.mp hza).symm.trans h)
      exact Or.inr ⟨z, ⟨⟨hz.1.1, hz.1.2, hzb⟩, by simpa only [coe_circleBranch] using hz.2⟩, rfl⟩
  calc
    _ ≤ ∫⁻ θ : UnitAddCircle, ∫⁻ γ,
        pathImageCount (S a θ) γ + pathImageCount (S b θ) γ ∂(μ : Measure _) :=
      lintegral_mono fun θ => lintegral_mono (hcover θ)
    _ = (∫⁻ θ : UnitAddCircle, ∫⁻ γ, pathImageCount (S a θ) γ ∂(μ : Measure _)) +
        (∫⁻ θ : UnitAddCircle, ∫⁻ γ, pathImageCount (S b θ) γ ∂(μ : Measure _)) := by
      simp_rw [lintegral_add_left (hmeas a _)]
      apply lintegral_add_left
      exact ((measurable_sigmaCompact_chart_circle_count (fun z : ℂ => π (z : Sphere))
        (hπ.comp OnePoint.continuous_coe) (hσ a) (circleBranch f a)
        ((hbranch a).continuousOn.mono inter_subset_right)).comp measurable_swap).lintegral_prod_right'
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hmean a, hmean b⟩

end CircleDomainRigidity

end

end OAI
