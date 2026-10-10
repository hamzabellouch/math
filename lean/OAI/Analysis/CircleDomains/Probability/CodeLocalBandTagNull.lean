import OAI.Analysis.CircleDomains.Probability.LawLocalBandTagNull
import OAI.Analysis.CircleDomains.Probability.CodeRealBandTagNull

namespace OAI

/-! The local branch payment theorem for the actual code law. The global
level's singleton contacts follow from stored tag tuples and ordered
compatibility, including when the coordinate has nonzero period. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [BorelSpace C(PathTime, Sphere)] in
theorem ae_code_level_singleton_on_tags
    (d : PathCodeData Sphere Sphere) (hH : ∀ i, IsClosed (d.levels i))
    (Free : Set Sphere) (hP : OrderedLevelNullCompatibility d.levels Free)
    (hunique : ∀ x ∈ Free, ∀ i a b,
      (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (P : ProbabilityMeasure (BasePathCode d)) (ω : TupleType → ℝ≥0∞)
    [SFinite (tupleReference ω)] (hτ : meanCodeTuple d P ≪ tupleReference ω) (i : ℕ) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ k t, t ∈ Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) →
        Γ.val.1 t ∈ Free → (θ, Γ.val.1 t) ∈ d.levels i →
        ¬ (connectedComponentIn {x | (θ, x) ∈ d.levels i} (Γ.val.1 t)).Nontrivial := by
  filter_upwards [ae_tag_contacts_singleton_at_independent_level d hH Free hP hunique
    P ω hτ i] with Γ hΓ
  filter_upwards [hΓ] with θ hθ
  intro k t ht hx hxt
  cases hslot : Γ.val.2 k with
  | inl u =>
      have hn : ¬ tagLeft (Sum.inl u) < t := not_lt_of_ge le_top
      exact (hn (hslot ▸ ht.1)).elim
  | inr q => exact hθ k q hslot t (hslot ▸ ht.1) (hslot ▸ ht.2) hx hxt

theorem ae_code_local_band_tag_trace_null
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
    (Flags : Set Sphere) (hFlags : Flags.Countable)
    (V : Set Sphere) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ closure V)
    (f : Sphere → ℝ) {M : ℝ} (hM : ∀ z ∈ d.quotientDomain, |f z| ≤ M)
    (hf : ContinuousOn f (d.quotientDomain ∩ V))
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    (P : ProbabilityMeasure (BasePathCode d))
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support m => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hband : ∀ z ∈ Flags ∩ V, ENNReal.ofReal
      (limsup f (𝓝[d.quotientDomain] z) - liminf f (𝓝[d.quotientDomain] z)) ≤ m z)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, m z = 0)
    (hH : ∀ i, IsClosed (d.levels i))
    (hP : OrderedLevelNullCompatibility d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ i a b,
      (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω) (i : ℕ)
    (hlevel : ∀ z ∈ V, ∀ θ,
      (z, θ) ∈ circleBandGraph d.quotientDomain f ↔ (θ, z) ∈ d.levels i)
    (trace : Sphere → ℝ)
    (htrace : ∀ z ∈ (d.quotientDomainᶜ \ Flags) ∩ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain f) ↔ t = trace z)
    {c : ℝ} (hbranch : ∀ z ∈ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain f) → t ∈ Ico c (c + 1)) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k,
      volume ((trace ∘ Γ.val.1) '' ((Γ.val.1 ⁻¹' (d.quotientDomainᶜ \ Flags)) ∩
        (Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩ Γ.val.1 ⁻¹' V))) = 0 := by
  apply ae_all_iff.mpr
  intro k
  apply ae_parameter_local_band_tag_null_trace hsard hsch hG hU hdense π hπ
    hclosed hsurj hr d.domainEquiv d.basePoint he hTD hbad hV hinfty hFlags hM hf
    (fun θ => {x | (θ, x) ∈ d.levels i})
    (fun θ => (hH i).preimage (continuous_const.prodMk continuous_id)) hlevel
    hv henergy P (codePath d) (measurable_codePath d) (codePathLaw d P) rfl
    (Eventually.of_forall fun Γ => Γ.property.1.1) ρ hρ
    ((meanPhysicalOccupation_codePathLaw d hU P).trans hocc) hρ2 m hm hweight hvisits
    hband hmFree (fun Γ => Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)))
    (fun _ => isOpen_Ioo) trace htrace hbranch
  filter_upwards [ae_code_level_singleton_on_tags d hH _ hP hunique P ω hτ i] with Γ hΓ
  filter_upwards [hΓ] with θ hθ
  exact fun t ht => hθ k t ht

end CircleDomainRigidity

end

end OAI
