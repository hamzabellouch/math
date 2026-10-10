import OAI.Analysis.CircleDomains.Probability.LawRealBandTagNull
import OAI.Analysis.CircleDomains.Selection.IndependentTagLevel
import OAI.Analysis.CircleDomains.Probability.CodeLawPhysicalOccupation
import OAI.Analysis.CircleDomains.Topology.FreeBandNeighborhoods

namespace OAI

/-! The real-coordinate tag conclusion for the actual base-code law.
The independent-level condition comes from the stored tag tuples; the
countable chart cover and all local payment measures are constructed.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [BorelSpace C(PathTime, Sphere)] in
theorem ae_code_real_level_singleton_on_tags
    (d : PathCodeData Sphere Sphere) (hH : ∀ i, IsClosed (d.levels i))
    (Free : Set Sphere) (hP : OrderedLevelNullCompatibility d.levels Free)
    (hunique : ∀ x ∈ Free, ∀ i a b,
      (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (P : ProbabilityMeasure (BasePathCode d)) (ω : TupleType → ℝ≥0∞)
    [SFinite (tupleReference ω)] (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (i : ℕ) (f : Sphere → ℝ)
    (hlevel : ∀ θ x, (θ, x) ∈ d.levels i ↔ (x, θ) ∈ circleBandGraph d.quotientDomain f) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ k t, t ∈ Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) →
        Γ.val.1 t ∈ Free → (Γ.val.1 t, θ) ∈ circleBandGraph d.quotientDomain f →
        ¬ (connectedComponentIn {x | (x, θ) ∈ circleBandGraph d.quotientDomain f}
          (Γ.val.1 t)).Nontrivial := by
  filter_upwards [ae_tag_contacts_singleton_at_independent_level d hH Free hP hunique
    P ω hτ i] with Γ hΓ
  filter_upwards [hΓ] with θ hθ
  intro k t ht hx hxt
  cases hslot : Γ.val.2 k with
  | inl u =>
      have hn : ¬ tagLeft (Sum.inl u) < t := not_lt_of_ge le_top
      exact (hn (hslot ▸ ht.1)).elim
  | inr q =>
      have hs : {x | (θ, x) ∈ d.levels i} =
          {x | (x, θ) ∈ circleBandGraph d.quotientDomain f} := by
        ext x
        exact hlevel θ x
      have h := hθ k q hslot t (hslot ▸ ht.1) (hslot ▸ ht.2) hx
        ((hlevel θ _).mpr hxt)
      simpa only [hs] using h

theorem ae_code_real_band_tag_trace_null
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere)
    (hG : IsOpen d.physicalDomain) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain)
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
    (m : Sphere → ℝ≥0∞) (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support m => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hband : ∀ z ∈ d.quotientDomainᶜ, ENNReal.ofReal
      (limsup f (𝓝[d.quotientDomain] z) - liminf f (𝓝[d.quotientDomain] z)) ≤ m z)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, m z = 0)
    (hH : ∀ i, IsClosed (d.levels i))
    (hP : OrderedLevelNullCompatibility d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ i a b,
      (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (i : ℕ)
    (hlevel : ∀ θ x, (θ, x) ∈ d.levels i ↔ (x, θ) ∈ circleBandGraph d.quotientDomain f) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k,
      volume (realBoundaryTrace d.quotientDomain f ''
        (Γ.val.1 '' Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩
          (d.quotientDomainᶜ \ Flags))) = 0 := by
  let Free := d.quotientDomainᶜ \ Flags
  let a := realBoundaryTrace d.quotientDomain f
  have htrace : ∀ x ∈ Free, ∀ t,
      (x, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain f) ↔ t = a x := by
    intro x hx
    apply real_band_fiber_eq_trace_of_zero_width hM (by rw [hdense.closure_eq]; exact mem_univ x)
    exact ENNReal.ofReal_eq_zero.mp (le_zero_iff.mp ((hband x hx.1).trans_eq (hmFree x hx)))
  obtain ⟨S, V, _, hSc, hcover, hV⟩ := countable_narrow_real_band_cover_closure
    (F := Free \ {π OnePoint.infty}) hM isClosed_singleton.isOpen_compl
    (fun _ hx => hx.2) (fun x hx t ht => (htrace x hx.1 t).mp ht)
  let : Countable S := hSc.to_subtype
  have hgood := ae_code_real_level_singleton_on_tags d hH Free hP hunique P ω hτ i f hlevel
  have hlocal : ∀ x : S, ∀ k : ℕ, ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      volume ((a ∘ Γ.val.1) ''
        ((Γ.val.1 ⁻¹' Free) ∩ (Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩
          Γ.val.1 ⁻¹' V x.val))) = 0 := by
    intro x k
    have hx := hV x.val x.property
    apply ae_parameter_real_band_tag_null_trace hsard hsch hG hU hdense π hπ
      hclosed hsurj hr d.domainEquiv d.basePoint he hTD hbad hx.1
      (fun h => (hx.2.2.1 h) (mem_singleton _)) hFlags hM hf hv henergy P
      (codePath d) (measurable_codePath d) (codePathLaw d P) rfl
      (Eventually.of_forall fun Γ => Γ.property.1.1) ρ hρ
      ((meanPhysicalOccupation_codePathLaw d hU P).trans hocc) hρ2 m hm hweight hvisits
      (fun z hz => hband z (hFlagsB hz)) hmFree
      (fun Γ => Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)))
      (fun _ => isOpen_Ioo) a (fun z hz => htrace z hz.1) hx.2.2.2
    filter_upwards [hgood] with Γ hΓ
    filter_upwards [hΓ] with θ hθ
    exact fun t ht => hθ k t ht
  have hall : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ x : S, ∀ k : ℕ,
      volume ((a ∘ Γ.val.1) ''
        ((Γ.val.1 ⁻¹' Free) ∩ (Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩
          Γ.val.1 ⁻¹' V x.val))) = 0 :=
    ae_all_iff.mpr fun x => ae_all_iff.mpr (hlocal x)
  filter_upwards [hall] with Γ hΓ
  intro k
  apply measure_mono_null (t := {a (π OnePoint.infty)} ∪ ⋃ x : S,
    (a ∘ Γ.val.1) '' ((Γ.val.1 ⁻¹' Free) ∩
      (Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩ Γ.val.1 ⁻¹' V x.val)))
  · rintro _ ⟨y, ⟨⟨t, ht, rfl⟩, hy⟩, rfl⟩
    by_cases heq : Γ.val.1 t = π OnePoint.infty
    · exact Or.inl (by simpa only [heq] using mem_singleton (a (π OnePoint.infty)))
    · obtain ⟨x, hx, htx⟩ := mem_iUnion₂.mp (hcover ⟨hy, heq⟩)
      exact Or.inr (mem_iUnion.mpr ⟨⟨x, hx⟩, t, ⟨hy, ht, htx⟩, rfl⟩)
  · exact measure_union_null (measure_singleton _) (measure_iUnion_null fun x => hΓ x k)

end CircleDomainRigidity

end

end OAI
