import OAI.Analysis.CircleDomains.Rigidity.CodeBranchFreeTrace

namespace OAI

/-! Free-point avoidance for a masked period coordinate. Narrow patches
are selected from its bounded branch atlas; none are assumed as extra data. All path-law and independent-level inputs are
those of the actual base code; no free-incidence conclusion is assumed. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem ae_code_period_free_level_incidence_null
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
    (M : Set Sphere) (hinftyM : π OnePoint.infty ∉ M)
    (hboundary : M \ interior M ⊆ d.quotientDomain)
    (b : Sphere) (hb : b ∈ Flags)
    (hmask : ∀ θ x, (θ, x) ∈ d.levels i → x ∈ M)
    (hcoverM : M \ {b} ⊆ ⋃ j, V j)
    (f : I → Sphere → ℝ) (bound : I → ℝ)
    (hbound : ∀ j z, z ∈ d.quotientDomain → |f j z| ≤ bound j)
    (hf : ∀ j, ContinuousOn (f j) (d.quotientDomain ∩ V j))
    (hv : ∀ j, ContDiffOn ℝ 1 (fun z : ℂ => f j (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V j))
    (henergy : ∀ j, (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V j,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f j (π (z : Sphere))) z‖ ^ 2) < ∞)
    (hband : ∀ j z, z ∈ (d.quotientDomainᶜ ∩ M) ∩ V j → ENNReal.ofReal
      (limsup (f j) (𝓝[d.quotientDomain] z) - liminf (f j) (𝓝[d.quotientDomain] z)) ≤
        d.levelWeights i z)
    (hlevel : ∀ j z, z ∈ M ∩ V j → ∀ θ,
      (z, θ) ∈ circleBandGraph d.quotientDomain (f j) ↔ (θ, z) ∈ d.levels i) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      volume {θ | ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i} = 0 := by
  let Free := d.quotientDomainᶜ \ Flags
  let F (j : I) := Free ∩ (M ∩ V j)
  let a (j : I) := realBoundaryTrace d.quotientDomain (f j)
  have htrace (j : I) (x : Sphere) (hx : x ∈ F j) :
      ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain (f j)) ↔ t = a j x := by
    apply real_band_fiber_eq_trace_of_zero_width (hbound j)
      (by rw [hdense.closure_eq]; trivial)
    exact ENNReal.ofReal_eq_zero.mp (le_zero_iff.mp
      ((hband j x ⟨⟨hx.1.1, hx.2.1⟩, hx.2.2⟩).trans_eq (hmFree x hx.1)))
  have hinside (x : Sphere) (hx : x ∈ Free ∩ M) : x ∈ interior M := by
    by_contra hn
    exact hx.1.1 (hboundary ⟨hx.2, hn⟩)
  have hselect (j : I) := countable_narrow_real_band_cover_closure
    (F := F j) (a := a j) (hbound j) ((hV j).inter isOpen_interior)
    (fun x hx => ⟨hx.2.2, hinside x ⟨hx.1, hx.2.1⟩⟩)
    (fun x hx t ht => (htrace j x hx t).mp ht)
  choose S N hSF hSc hcov hN using hselect
  let : ∀ j, Countable (S j) := fun j => (hSc j).to_subtype
  let J := Σ j, S j
  have hNV (q : J) : N q.1 q.2.val ⊆ V q.1 :=
    fun x hx => ((hN q.1 q.2.val q.2.property).2.2.1 (subset_closure hx)).1
  have hNM (q : J) : N q.1 q.2.val ⊆ M :=
    fun x hx => interior_subset (((hN q.1 q.2.val q.2.property).2.2.1 (subset_closure hx)).2)
  apply ae_code_branch_free_level_incidence_null hsard hsch d hG hU hdense hdust
    π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB P ρ hρ hocc hρ2
    i hm hweight hvisits hmFree hdeleteCover hdeletions hH hP hunique ω hτ
    (fun q : J => N q.1 q.2.val)
    (fun q => (hN q.1 q.2.val q.2.property).1)
    (fun q hp => hinftyM (interior_subset
      (((hN q.1 q.2.val q.2.property).2.2.1 hp).2)))
    (fun q => f q.1) (fun q => bound q.1) (fun q => hbound q.1)
    (fun q => (hf q.1).mono (fun x hx => ⟨hx.1, hNV q hx.2⟩))
    (fun q => (hv q.1).mono (fun x hx => ⟨hx.1, hNV q hx.2⟩))
    (fun q => (lintegral_mono_set (show
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' N q.1 q.2.val) ⊆
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V q.1) from
        fun x hx => ⟨hx.1, hNV q hx.2⟩)).trans_lt (henergy q.1))
    (fun q z hz => hband q.1 z ⟨⟨hz.1, hNM q hz.2⟩, hNV q hz.2⟩)
    (fun q => a q.1 q.2.val - 1 / 2)
    (fun q => (hN q.1 q.2.val q.2.property).2.2.2)
    (fun q z hz => hlevel q.1 z ⟨hNM q hz, hNV q hz⟩)
  intro x hx θ hθ
  have hxM := hmask θ x hθ
  have hxb : x ≠ b := fun heq => hx.2 (heq ▸ hb)
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcoverM ⟨hxM, hxb⟩)
  obtain ⟨y, hyS, hxy⟩ := mem_iUnion₂.mp (hcov j ⟨hx, hxM, hj⟩)
  exact ⟨⟨j, ⟨y, hyS⟩⟩, hxy⟩

end CircleDomainRigidity

end

end OAI
