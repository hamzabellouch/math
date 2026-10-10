import OAI.Analysis.CircleDomains.Selection.CodePeriodGenericLevels
import OAI.Analysis.CircleDomains.Selection.RankedIndependentLevel

namespace OAI

/-! Generic prior-level intersections for a code whose natural labels carry
an independent inherited order. Physical coarea and local trace estimates
are unchanged; only the finite-tuple comparison uses the rank. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [BorelSpace C(PathTime, Sphere)] in
theorem ranked_ae_code_level_singleton_on_tags
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (d : PathCodeData Sphere Sphere) (hH : ∀ i, IsClosed (d.levels i))
    (Free : Set Sphere) (hP : RankedLevelNullCompatibility rank d.levels Free)
    (hunique : ∀ x ∈ Free, ∀ i a b,
      (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (P : ProbabilityMeasure (BasePathCode d)) (ω : TupleType → ℝ≥0∞)
    [SFinite (tupleReference ω)] (hτ : meanCodeTuple d P ≪ tupleReference ω) (i : ℕ) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ k t, t ∈ Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) →
        Γ.val.1 t ∈ Free → (θ, Γ.val.1 t) ∈ d.levels i →
        ¬ (connectedComponentIn {x | (θ, x) ∈ d.levels i} (Γ.val.1 t)).Nontrivial := by
  filter_upwards [ae_ranked_tag_contacts_singleton_at_independent_level rank hrank d hH Free hP hunique
    P ω hτ i] with Γ hΓ
  filter_upwards [hΓ] with θ hθ
  intro k t ht hx hxt
  cases hslot : Γ.val.2 k with
  | inl u =>
      have hn : ¬ tagLeft (Sum.inl u) < t := not_lt_of_ge le_top
      exact (hn (hslot ▸ ht.1)).elim
  | inr q => exact hθ k q hslot t (hslot ▸ ht.1) (hslot ▸ ht.2) hx hxt

theorem ranked_ae_code_local_band_tag_trace_null
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
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
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
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
  filter_upwards [ranked_ae_code_level_singleton_on_tags rank hrank d hH _ hP hunique P ω hτ i] with Γ hΓ
  filter_upwards [hΓ] with θ hθ
  exact fun t ht => hθ k t ht


theorem ranked_ae_code_branch_free_level_incidence_null
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
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
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
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
  exact ranked_ae_code_local_band_tag_trace_null rank hrank hsard hsch d hG hU hdense π hπ
    hclosed hsurj hr he hTD hbad Flags hFlags (V j) (hV j) (hinfty j)
    (f j) (hbound j) (hf j) (hv j) (henergy j) P ρ hρ hocc hρ2
    (d.levelWeights i) hm hweight hvisits
    (fun z hz => hband j z ⟨hFlagsB hz.1, hz.2⟩) hmFree hH hP hunique ω hτ i
    (hlevel j) (trace j) (htrace j) (hbranch j)


theorem ranked_ae_code_period_free_level_incidence_null
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
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
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
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
  apply ranked_ae_code_branch_free_level_incidence_null rank hrank hsard hsch d hG hU hdense hdust
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


theorem ranked_code_period_generic_levels
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
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
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    {I : Type*} [Countable I] (V : I → Set Sphere) (hV : ∀ j, IsOpen (V j))
    (M : Set Sphere) (hM : IsClosed M) (hinftyM : π OnePoint.infty ∉ M)
    (hboundary : M \ interior M ⊆ d.quotientDomain)
    (b : Sphere) (hb : b ∈ Flags) (hbWeight : 1 ≤ d.levelWeights i b)
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
      (z, θ) ∈ circleBandGraph d.quotientDomain (f j) ↔ (θ, z) ∈ d.levels i)
    (w : Sphere → UnitAddCircle)
    (hw : ∀ j x, x ∈ d.quotientDomain ∩ V j → (f j x : UnitAddCircle) = w x)
    (D : Set ℂ) (hD : IsOpen D) (hDG : ∀ z ∈ D, (z : Sphere) ∈ d.physicalDomain)
    (hDcover : ∀ z : ℂ, (z : Sphere) ∈ d.physicalDomain → π (z : Sphere) ∈ M → z ∈ D)
    (F : ℂ → UnitAddCircle) (hF : FiniteTransfer.SmoothCircleOn F D)
    (hFpull : ∀ z ∈ D, F z = w (π (z : Sphere)))
    (hFenergy : (∫⁻ z in D, ENNReal.ofReal ‖FiniteTransfer.circleFDeriv F z‖ ^ 2) < ∞) :
    (∫⁻ θ : UnitAddCircle, ∫⁻ Γ : BasePathCode d,
      pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1 ∂(P : Measure _)) < ∞ ∧
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ Γ : BasePathCode d, pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1
        ∂(P : Measure _)) < ∞ ∧
      ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        ¬ ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
  have hfree := ranked_ae_code_period_free_level_incidence_null rank hrank hsard hsch d hG hU hdense hdust
    π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB P ρ hρ hocc hρ2
    i hm hweight hvisits hmFree hdeleteCover hdeletions hH hP hunique ω hτ
    V hV M hinftyM hboundary b hb hmask hcoverM f bound hbound hf hv henergy hband hlevel
  have hfinite : ∀ᵐ γ ∂(codePathLaw d P : Measure C(PathTime, Sphere)),
      physicalDomainLength d.domainEquiv d.basePoint γ < ∞ := by
    change ∀ᵐ γ ∂(P : Measure (BasePathCode d)).map (codePath d), _
    apply (ae_map_iff (measurable_codePath d).aemeasurable
      (measurableSet_finitePhysicalDomainLength d.domainEquiv hU d.basePoint)).mpr
    exact Eventually.of_forall fun Γ => Γ.property.1.1
  have hdomLevel (θ : UnitAddCircle) (x : Sphere)
      (hx : x ∈ d.quotientDomain ∩ {x | (θ, x) ∈ d.levels i}) : x ∈ M ∧ w x = θ := by
    have hxM := hmask θ x hx.2
    have hxb : x ≠ b := fun heq => hFlagsB hb (heq ▸ hx.1)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcoverM ⟨hxM, hxb⟩)
    have hcg := (hlevel j x ⟨hxM, hj⟩ θ).mpr hx.2
    have heq := (circleBandGraph_of_continuousAt
      ((hf j).continuousAt ((hU.inter (hV j)).mem_nhds ⟨hx.1, hj⟩)) hx.1 θ).mp hcg
    exact ⟨hxM, (hw j x ⟨hx.1, hj⟩).symm.trans heq⟩
  have hdom := mean_masked_circle_domain_count_finite hcoarea d.domainEquiv hU d.basePoint
    π hπ he M hM hinftyM (fun θ => {x | (θ, x) ∈ d.levels i}) w hdomLevel
    D hD hDG hDcover F hF hFpull hFenergy (codePathLaw d P) hfinite ρ hρ
    ((meanPhysicalOccupation_codePathLaw d hU P).trans hocc) hρ2
  have hvol : ∀ x ∈ Flags, volume {θ : UnitAddCircle | (θ, x) ∈ d.levels i} ≤ d.levelWeights i x := by
    intro x hx
    by_cases hxM : x ∈ M
    · by_cases hxb : x = b
      · subst x
        exact (measure_mono (subset_univ _)).trans (by simpa [AddCircle.measure_univ] using hbWeight)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp (hcoverM ⟨hxM, hxb⟩)
        have heq : {θ : UnitAddCircle | (θ, x) ∈ d.levels i} =
            {θ | (x, θ) ∈ circleBandGraph d.quotientDomain (f j)} :=
          Set.ext fun θ => (hlevel j x ⟨hxM, hj⟩ θ).symm
        rw [heq]
        exact (volume_circleBandGraph_incidence_le_budget (hbound j)
          (by rw [hdense.closure_eq]; trivial) le_rfl).trans
            (hband j x ⟨⟨hFlagsB hx, hxM⟩, hj⟩)
    · have hempty : {θ : UnitAddCircle | (θ, x) ∈ d.levels i} = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun θ hθ => hxM (hmask θ x hθ)
      rw [hempty, measure_empty]
      exact bot_le
  have hflag := mean_flag_intersection_count_finite_of_support (hH i) Flags hFlags
    (d.levelWeights i) hvol (codePathLaw d P) hm hweight hvisits
  have hσU : IsSigmaCompact d.quotientDomain := by
    let : LocallyCompactSpace d.quotientDomain := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  have hfree' : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ¬ ∃ x ∈ range (codePath d Γ) ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
    filter_upwards [hfree] with Γ hΓ
    exact ae_iff.mpr (by simpa only [not_not, codePath] using hΓ)
  have hbnd := mean_parameter_level_count_le_of_no_free_hits (hH i)
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
  have hmean : (∫⁻ θ : UnitAddCircle, ∫⁻ Γ : BasePathCode d,
      pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1 ∂(P : Measure _)) < ∞ := by
    apply hbnd.trans_lt
    apply ENNReal.add_lt_top.mpr
    constructor
    · simpa only [hdint] using hdom
    · simpa only [hfint] using hflag
  refine ⟨hmean, ?_⟩
  have hdisj : Disjoint d.quotientDomain Flags :=
    disjoint_left.mpr fun x hx hxf => hFlagsB hxf hx
  simpa only [codePath] using ae_level_parameter_free_avoidance (hH i)
    d.quotientDomain Flags hσU hFlags hdisj P (codePath d) (measurable_codePath d) hfree' hmean


end CircleDomainRigidity

end

end OAI
