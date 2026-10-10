import OAI.Analysis.CircleDomains.Probability.CodeRealBandTagNull
import OAI.Analysis.CircleDomains.Rigidity.CodeFreeTrace
import OAI.Analysis.CircleDomains.Rigidity.TraceBandLevel

namespace OAI

/-! The free-boundary part of the generic-level theorem for an actual
real coordinate and an actual coded law, including the residual times.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem ae_code_real_free_level_incidence_null
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
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), volume
      {θ | ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i} = 0 := by
  let Free := d.quotientDomainᶜ \ Flags
  let w : Sphere → UnitAddCircle := fun x => (realBoundaryTrace d.quotientDomain f x : UnitAddCircle)
  have hzero (x : Sphere) (hx : x ∈ Free) :
      limsup f (𝓝[d.quotientDomain] x) - liminf f (𝓝[d.quotientDomain] x) ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp (le_zero_iff.mp ((hband x hx.1).trans_eq (hmFree x hx)))
  have htrace : ∀ x ∈ Free, ∀ t, (t, x) ∈ d.levels i ↔ w x = t := by
    intro x hx t
    rw [hlevel]
    exact circleBandGraph_of_trace hM (by rw [hdense.closure_eq]; exact mem_univ x)
      (tendsto_boundaryTrace_of_zero_band hM
        (by rw [hdense.closure_eq]; exact mem_univ x) (hzero x hx))
  have htags := ae_code_real_band_tag_trace_null hsard hsch d hG hU hdense π hπ
    hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB f hM hf hv henergy P ρ hρ hocc hρ2
    (d.levelWeights i) hm hweight hvisits hband hmFree hH hP hunique ω hτ i hlevel
  apply ae_code_free_level_incidence_null d P i Free
    (fun x hx => hdust.symm ▸ hx.1) w htrace hm hweight hvisits hcover
    (fun n => disjoint_left.mpr fun x hx hp => hx.2 (hdeletions n hp))
  filter_upwards [htags] with Γ hΓ
  intro k
  simpa only [w, image_image, Function.comp_def] using volume_addCircle_image_eq_zero (hΓ k)

end CircleDomainRigidity

end

end OAI
