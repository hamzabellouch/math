import OAI.Analysis.CircleDomains.Rigidity.CodeRealFreeTrace
import OAI.Analysis.CircleDomains.Selection.RealDomainIntersections
import OAI.Analysis.CircleDomains.Selection.FiniteFlagIntersections
import OAI.Analysis.CircleDomains.Probability.BandMeasure
import OAI.Analysis.CircleDomains.Selection.MeanLevelAssembly
import OAI.Analysis.CircleDomains.Selection.CodeRealMeanIntersections
import OAI.Analysis.CircleDomains.Probability.LevelLawQuantifiers

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

theorem code_real_generic_levels
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
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ Γ : BasePathCode d, pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1
        ∂(P : Measure _)) < ∞ ∧
      ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        ¬ ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
  have hmean := mean_code_real_level_intersections_finite hcoarea hsard hsch d
    hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB f hM hf hv henergy
    hK hzero hinfty P ρ hρ hocc hρ2 i hm hweight hvisits hband hmFree hcover hdeletions
    hH hP hunique ω hτ hlevel
  have hfree := ae_code_real_free_level_incidence_null hsard hsch d hG hU hdense hdust
    π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB f hM hf hv henergy P ρ hρ hocc hρ2
    i hm hweight hvisits hband hmFree hcover hdeletions hH hP hunique ω hτ hlevel
  have hσU : IsSigmaCompact d.quotientDomain := by
    let : LocallyCompactSpace d.quotientDomain := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  have hfree' : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ¬ ∃ x ∈ range (codePath d Γ) ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
    filter_upwards [hfree] with Γ hΓ
    exact ae_iff.mpr (by simpa only [not_not, codePath] using hΓ)
  have hdisj : Disjoint d.quotientDomain Flags :=
    disjoint_left.mpr fun x hx hxf => hFlagsB hxf hx
  simpa only [codePath] using ae_level_parameter_free_avoidance (hH i)
    d.quotientDomain Flags hσU hFlags hdisj P (codePath d) (measurable_codePath d) hfree' hmean

end CircleDomainRigidity

end

end OAI
