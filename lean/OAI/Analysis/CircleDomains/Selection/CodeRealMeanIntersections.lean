import OAI.Analysis.CircleDomains.Rigidity.CodeRealFreeTrace
import OAI.Analysis.CircleDomains.Selection.RealDomainIntersections
import OAI.Analysis.CircleDomains.Selection.FiniteFlagIntersections
import OAI.Analysis.CircleDomains.Probability.BandMeasure
import OAI.Analysis.CircleDomains.Selection.MeanLevelAssembly

namespace OAI

/-! Generic prior-level intersections for real coordinates under a base-code
law, with physical, flagged, and free contributions. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem mean_code_real_level_intersections_finite
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere)
    (hG : IsOpen d.physicalDomain) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hdust : d.dust = d.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hTD : IsTotallyDisconnected d.quotientDomainᶜ)
    (hbad : ∀ p ∈ d.physicalDomainᶜ, π p ∈ d.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ d.quotientDomainᶜ)
    (f : Sphere → ℝ) {M : ℝ} (hM : ∀ z ∈ d.quotientDomain, |f z| ≤ M)
    (hf : ContinuousOn f d.quotientDomain)
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ d.physicalDomain → z ∉ K → f (π (z : Sphere)) = 0)
    (hinfty : OnePoint.infty ∈ d.physicalDomain → f (π OnePoint.infty) = 0)
    (P : ProbabilityMeasure (BasePathCode d))
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hband : ∀ z ∈ d.quotientDomainᶜ, ENNReal.ofReal
      (limsup f (𝓝[d.quotientDomain] z) - liminf f (𝓝[d.quotientDomain] z)) ≤
        d.levelWeights i z)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hcover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : OrderedLevelNullCompatibility d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (hlevel : ∀ θ x, (θ, x) ∈ d.levels i ↔ (x, θ) ∈ circleBandGraph d.quotientDomain f) :
    (∫⁻ θ : UnitAddCircle, ∫⁻ Γ : BasePathCode d,
      pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1 ∂(P : Measure _)) < ∞ := by
  have hfree := ae_code_real_free_level_incidence_null hsard hsch d hG hU hdense hdust
    π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB f hM hf hv henergy P ρ hρ hocc hρ2
    i hm hweight hvisits hband hmFree hcover hdeletions hH hP hunique ω hτ hlevel
  have hfinite : ∀ᵐ γ ∂(codePathLaw d P : Measure C(PathTime, Sphere)),
      physicalDomainLength d.domainEquiv d.basePoint γ < ∞ := by
    change ∀ᵐ γ ∂(P : Measure (BasePathCode d)).map (codePath d), _
    apply (ae_map_iff (measurable_codePath d).aemeasurable
      (measurableSet_finitePhysicalDomainLength d.domainEquiv hU d.basePoint)).mpr
    exact Eventually.of_forall fun Γ => Γ.property.1.1
  have hdom := mean_real_domain_circle_count_finite hcoarea hG d.domainEquiv hU d.basePoint π hπ he
    f hf hv henergy hK hzero hinfty (codePathLaw d P) hfinite ρ hρ
    ((meanPhysicalOccupation_codePathLaw d hU P).trans hocc) hρ2
  have hvol : ∀ x ∈ Flags, volume {θ : UnitAddCircle | (θ, x) ∈ d.levels i} ≤ d.levelWeights i x := by
    intro x hx
    have heq : {θ : UnitAddCircle | (θ, x) ∈ d.levels i} =
        {θ : UnitAddCircle | (x, θ) ∈ circleBandGraph d.quotientDomain f} :=
      Set.ext fun θ => hlevel θ x
    rw [heq]
    exact (volume_circleBandGraph_incidence_le_budget hM
      (by rw [hdense.closure_eq]; exact mem_univ x) le_rfl).trans (hband x (hFlagsB hx))
  have hflag := mean_flag_intersection_count_finite_of_support (hH i) Flags hFlags
    (d.levelWeights i) hvol (codePathLaw d P) hm hweight hvisits
  have hσU : IsSigmaCompact d.quotientDomain := by
    let : LocallyCompactSpace d.quotientDomain := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  have hfree' : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ¬ ∃ x ∈ range (codePath d Γ) ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
    filter_upwards [hfree] with Γ hΓ
    exact ae_iff.mpr (by simpa only [not_not, codePath] using hΓ)
  have hb := mean_parameter_level_count_le_of_no_free_hits (hH i)
    d.quotientDomain Flags hσU hFlags P (codePath d) (measurable_codePath d) hfree'
  have hDmeas := measurable_sigmaCompact_restricted_relation_path_count hσU
    ((hH i).preimage continuous_swap)
  have hFmeas := measurable_flag_intersection_count (hH i) Flags hFlags
  have hdint (θ : UnitAddCircle) :
      (∫⁻ Γ : BasePathCode d, pathImageCount (d.quotientDomain ∩ {x | (θ, x) ∈ d.levels i})
        (codePath d Γ) ∂(P : Measure _)) =
      ∫⁻ γ, pathImageCount (d.quotientDomain ∩ {x | (θ, x) ∈ d.levels i}) γ
        ∂(codePathLaw d P : Measure _) := by
    have hmeas : Measurable (fun γ : C(PathTime, Sphere) =>
        pathImageCount (d.quotientDomain ∩ {x | (θ, x) ∈ d.levels i}) γ) :=
      hDmeas.comp (measurable_id.prodMk measurable_const)
    rw [codePathLaw, ProbabilityMeasure.toMeasure_map]
    exact (lintegral_map hmeas (measurable_codePath d)).symm
  have hfint (θ : UnitAddCircle) :
      (∫⁻ Γ : BasePathCode d, pathImageCount (Flags ∩ {x | (θ, x) ∈ d.levels i})
        (codePath d Γ) ∂(P : Measure _)) =
      ∫⁻ γ, pathImageCount (Flags ∩ {x | (θ, x) ∈ d.levels i}) γ
        ∂(codePathLaw d P : Measure _) := by
    have hmeas : Measurable (fun γ : C(PathTime, Sphere) =>
        pathImageCount (Flags ∩ {x | (θ, x) ∈ d.levels i}) γ) :=
      hFmeas.comp (measurable_id.prodMk measurable_const)
    rw [codePathLaw, ProbabilityMeasure.toMeasure_map]
    exact (lintegral_map hmeas (measurable_codePath d)).symm
  apply hb.trans_lt
  apply ENNReal.add_lt_top.mpr
  constructor
  · simp_rw [hdint]
    simpa only [hlevel] using hdom
  · simpa only [hfint] using hflag

end CircleDomainRigidity

end

end OAI
