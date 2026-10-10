import OAI.Analysis.CircleDomains.Modulus.LocalBandIncidence

namespace OAI

/-! Free-point avoidance for a prior coordinate described by countably
many local real branches. All path-law and independent-level inputs are
those of the actual base code; no free-incidence conclusion is assumed. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem ae_code_branch_free_level_incidence_null
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
    (P : ProbabilityMeasure (BasePathCode d))
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) => d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support (d.levelWeights i) => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hdeleteCover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : OrderedLevelNullCompatibility d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    {I : Type*} [Countable I] (V : I → Set Sphere) (hV : ∀ j, IsOpen (V j))
    (hinfty : ∀ j, π OnePoint.infty ∉ closure (V j))
    (f : I → Sphere → ℝ) (bound : I → ℝ)
    (hbound : ∀ j z, z ∈ d.quotientDomain → |f j z| ≤ bound j)
    (hf : ∀ j, ContinuousOn (f j) (d.quotientDomain ∩ V j))
    (hv : ∀ j, ContDiffOn ℝ 1 (fun z : ℂ => f j (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V j))
    (henergy : ∀ j, (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V j,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f j (π (z : Sphere))) z‖ ^ 2) < ∞)
    (hband : ∀ j z, z ∈ d.quotientDomainᶜ ∩ V j → ENNReal.ofReal
      (limsup (f j) (𝓝[d.quotientDomain] z) - liminf (f j) (𝓝[d.quotientDomain] z)) ≤
        d.levelWeights i z)
    (c : I → ℝ) (hbranch : ∀ j z, z ∈ V j → ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain (f j)) → t ∈ Ico (c j) (c j + 1))
    (hlevel : ∀ j z, z ∈ V j → ∀ θ,
      (z, θ) ∈ circleBandGraph d.quotientDomain (f j) ↔ (θ, z) ∈ d.levels i)
    (hcover : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ θ, (θ, x) ∈ d.levels i → ∃ j, x ∈ V j) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      volume {θ | ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i} = 0 := by
  let trace (j : I) := realBoundaryTrace d.quotientDomain (f j)
  have htrace (j : I) (x : Sphere) (hx : x ∈ (d.quotientDomainᶜ \ Flags) ∩ V j) :
      ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain (f j)) ↔ t = trace j x := by
    apply real_band_fiber_eq_trace_of_zero_width (hbound j)
      (by rw [hdense.closure_eq]; trivial)
    exact ENNReal.ofReal_eq_zero.mp (le_zero_iff.mp
      ((hband j x ⟨hx.1.1, hx.2⟩).trans_eq (hmFree x hx.1)))
  apply ae_code_free_incidence_null_of_local_real_traces d P i (d.quotientDomainᶜ \ Flags)
    (fun x hx => hdust.symm ▸ hx.1) hm hweight hvisits hdeleteCover
    (fun n => disjoint_left.mpr fun x hx hxn => hx.2 (hdeletions n hxn))
    V f trace hcover hlevel htrace
  intro j
  exact ae_code_local_band_tag_trace_null hsard hsch d hG hU hdense π hπ
    hclosed hsurj hr he hTD hbad Flags hFlags (V j) (hV j) (hinfty j)
    (f j) (hbound j) (hf j) (hv j) (henergy j) P ρ hρ hocc hρ2
    (d.levelWeights i) hm hweight hvisits
    (fun z hz => hband j z ⟨hFlagsB hz.1, hz.2⟩) hmFree hH hP hunique ω hτ i
    (hlevel j) (trace j) (htrace j) (hbranch j)

end CircleDomainRigidity

end

end OAI
