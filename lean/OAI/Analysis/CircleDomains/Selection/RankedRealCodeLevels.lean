import OAI.Analysis.CircleDomains.Selection.CodeRealGenericLevels
import OAI.Analysis.CircleDomains.Selection.RankedIndependentLevel

namespace OAI

/-! Real-coordinate generic levels with the inherited order on code labels. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [BorelSpace C(PathTime, Sphere)] in
theorem ranked_ae_code_real_level_singleton_on_tags
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (d : PathCodeData Sphere Sphere) (hH : ∀ i, IsClosed (d.levels i))
    (Free : Set Sphere) (hP : RankedLevelNullCompatibility rank d.levels Free)
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
  filter_upwards [ae_ranked_tag_contacts_singleton_at_independent_level rank hrank d hH Free hP hunique
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

theorem ranked_ae_code_real_band_tag_trace_null
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
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
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
  have hgood := ranked_ae_code_real_level_singleton_on_tags rank hrank d hH Free hP hunique P ω hτ i f hlevel
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


theorem ranked_ae_code_real_free_level_incidence_null
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
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
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
  have htags := ranked_ae_code_real_band_tag_trace_null rank hrank hsard hsch d hG hU hdense π hπ
    hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB f hM hf hv henergy P ρ hρ hocc hρ2
    (d.levelWeights i) hm hweight hvisits hband hmFree hH hP hunique ω hτ i hlevel
  apply ae_code_free_level_incidence_null d P i Free
    (fun x hx => hdust.symm ▸ hx.1) w htrace hm hweight hvisits hcover
    (fun n => disjoint_left.mpr fun x hx hp => hx.2 (hdeletions n hp))
  filter_upwards [htags] with Γ hΓ
  intro k
  simpa only [w, image_image, Function.comp_def] using volume_addCircle_image_eq_zero (hΓ k)


theorem ranked_mean_code_real_level_intersections_finite
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
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (hlevel : ∀ θ x, (θ, x) ∈ d.levels i ↔ (x, θ) ∈ circleBandGraph d.quotientDomain f) :
    (∫⁻ θ : UnitAddCircle, ∫⁻ Γ : BasePathCode d,
      pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1 ∂(P : Measure _)) < ∞ := by
  have hfree := ranked_ae_code_real_free_level_incidence_null rank hrank hsard hsch d hG hU hdense hdust
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


theorem ranked_code_real_generic_levels
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
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
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
  have hmean := ranked_mean_code_real_level_intersections_finite rank hrank hcoarea hsard hsch d
    hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB f hM hf hv henergy
    hK hzero hinfty P ρ hρ hocc hρ2 i hm hweight hvisits hband hmFree hcover hdeletions
    hH hP hunique ω hτ hlevel
  have hfree := ranked_ae_code_real_free_level_incidence_null rank hrank hsard hsch d hG hU hdense hdust
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
