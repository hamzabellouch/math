import OAI.Analysis.CircleDomains.Selection.CountableUnavailableLevelEndpoints
import OAI.Analysis.CircleDomains.Selection.RankedDiffuseIntersections

namespace OAI

/-! Endpoint-law recursion with the inherited order on the selected levels.
The positive-law construction and disk-crossing input are unchanged. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem RecursiveCodeLaw.ranked_countable_contacts
    {R : Type*} [LinearOrder R] (rank : ℕ → R) (hrank : Injective rank)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {flags : Set Sphere} {ω : TupleType → ℝ≥0∞} [SFinite (tupleReference ω)]
    (L M : RecursiveCodeLaw base π flags ω)
    (hB : IsClosed base.dust) (hflags : flags.Countable)
    (hH : ∀ i, IsClosed (base.levels i))
    (hweights : ∀ i, (∑' x, base.levelWeights i x ^ 2) < ∞)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ flags)
    (hcompat : RankedLevelNullCompatibility rank base.levels (base.dust \ flags))
    (hunique : ∀ x ∈ base.dust \ flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (i : ℕ) (hprior : M.data.priorLaws i = (codePathLaw L.data L.law : Measure C(PathTime, Sphere))) :
    ∃ D : Set Sphere, D.Countable ∧
      ∀ᵐ z ∂((L.law : Measure (BasePathCode L.data)).prod
        (M.law : Measure (BasePathCode M.data))),
        range z.1.val.1 ∩ range z.2.val.1 ∩ L.data.dust ⊆ D := by
  have hde : M.data.dust = L.data.dust := M.dust_eq.trans L.dust_eq.symm
  have heq : support (dustPriorHitMass M.data.dust (M.data.priorLaws i)) =
      {x | x ∈ L.data.dust ∧ 0 < codeHitProbability L.data L.law x} := by
    rw [hde, hprior, support_dustPriorHitMass]
    ext x
    simp only [mem_inter_iff, mem_support, priorHitMass_codePathLaw, mem_ofPred_eq,
      pos_iff_ne_zero]
  have hm : (support (dustPriorHitMass M.data.dust (M.data.priorLaws i))).Countable :=
    heq.symm ▸ L.countable_dust_hits
  have hw : countingSquareNorm (fun x : support
      (dustPriorHitMass M.data.dust (M.data.priorLaws i)) =>
        dustPriorHitMass M.data.dust (M.data.priorLaws i) x.val) < ∞ := by
    rw [M.dust_eq, hprior]
    exact dust_prior_weight_norm_finite L.data L.law base.dust L.hit_square_finite
  have hv : countingSquareNorm (fun x : support
      (dustPriorHitMass M.data.dust (M.data.priorLaws i)) =>
        meanVisitCount (codePathLaw M.data M.law) x.val) < ∞ := by
    rw [M.dust_eq]
    exact M.prior_visit_norm_finite i
  have hc : ∀ x ∈ support (dustPriorHitMass M.data.dust (M.data.priorLaws i)),
      ∀ᶠ n in atTop, x ∈ M.data.priorDeletions i n := by
    intro x hx
    rw [support_dustPriorHitMass] at hx
    simpa only [M.prior_deletions_eq] using M.presentation.prior_cover i x hx.2
  have hs : ∀ n, (M.data.priorDeletions i n : Set Sphere) ⊆
      support (priorHitMass (M.data.priorLaws i)) := by
    intro n
    simpa only [M.prior_deletions_eq] using M.presentation.prior_subset i n
  have hf : ∀ n, (L.data.flagDeletions n : Set Sphere) ⊆ flags := by
    intro n
    simpa only [L.flag_deletions_eq] using L.presentation.flag_subset n
  have hlcount (j : ℕ) : (support (L.data.levelWeights j)).Countable := by
    rw [L.weights_eq]
    exact hflags.mono (hmarked j)
  have hlweight (j : ℕ) : countingSquareNorm (fun x : support (L.data.levelWeights j) =>
      L.data.levelWeights j x.val) < ∞ := by
    rw [L.weights_eq]
    apply (countingSquareNorm_comp_injective (base.levelWeights j)
      (fun x : support (base.levelWeights j) => x.val) Subtype.val_injective).trans_lt
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hweights j).ne
  have hlvisit (j : ℕ) : countingSquareNorm (fun x : support (L.data.levelWeights j) =>
      meanVisitCount (codePathLaw L.data L.law) x.val) < ∞ := by
    rw [L.weights_eq]
    exact L.flag_visit_norm_finite j (hmarked j)
  have hlcover : ∀ j x, x ∈ support (L.data.levelWeights j) →
      ∀ᶠ n in atTop, x ∈ L.data.flagDeletions n := by
    intro j x hx
    rw [L.weights_eq] at hx
    simpa only [L.flag_deletions_eq] using L.presentation.flag_cover x (hmarked j hx)
  have hraw := ae_ranked_diffuse_dust_intersections_of_dust_bounds rank hrank L.data M.data
    (by simpa only [L.dust_eq] using hB) hde
    (by simpa only [L.levels_eq] using hH) (M.levels_eq.trans L.levels_eq.symm)
    L.law M.law i hprior hm hw hv hc hs flags hf hlcount hlweight hlvisit hlcover
    (by simpa only [L.levels_eq, L.dust_eq] using hcompat)
    (by simpa only [L.levels_eq, L.dust_eq] using hunique)
    ω L.tuple_absolutelyContinuous M.tuple_absolutelyContinuous
  refine ⟨flags ∪ support (dustPriorHitMass M.data.dust (M.data.priorLaws i)),
    hflags.union hm, ?_⟩
  filter_upwards [hraw] with z hz
  intro x hx
  rcases hz hx with hxf | hxp
  · exact Or.inl hxf
  · right
    rw [support_dustPriorHitMass]
    exact ⟨hde.symm ▸ hx.2, hxp⟩


theorem ranked_countable_recursive_code_laws
    {R : Type*} [LinearOrder R] (rank : ℕ → R) (hrank : Injective rank) {I : Type*} [LinearOrder I]
    (hcross : UnitDiskAlternatingContinua)
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdisj : Disjoint base.quotientDomain base.dust) (hBU : base.dustᶜ ⊆ base.quotientDomain)
    (hB : IsClosed base.dust) (hTD : IsTotallyDisconnected base.dust)
    (hE : IsClosed base.anchor) (hEU : base.anchor ⊆ base.quotientDomain)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hbad : ∀ x ∈ base.physicalDomainᶜ, π x ∈ base.dust)
    (hinf : π OnePoint.infty ∉ base.dust)
    (flags : Set Sphere) (hflags : flags.Countable)
    (hH : ∀ i, IsClosed (base.levels i))
    (hweights : ∀ i, (∑' x, base.levelWeights i x ^ 2) < ∞)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ flags)
    (hcompat : RankedLevelNullCompatibility rank base.levels (base.dust \ flags))
    (hunique : ∀ x ∈ base.dust \ flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (L : I → RecursiveCodeLaw base π flags ω)
    (hfinite : ∀ i, (L i).data.target ≠ OnePoint.infty)
    (hinj : Injective (fun i => (L i).data.target))
    (hprior : ∀ i j, i < j → ∃ n,
      (L j).data.priorLaws n = (codePathLaw (L i).data (L i).law : Measure C(PathTime, Sphere))) : Countable I := by
  let : ∀ i, IsFiniteMeasure (meanCodeOccupation (L i).data (L i).law) :=
    fun i => (L i).finite_occupation
  apply countable_quotient_code_laws hcross hcoarea hsard hsch
    base.physicalDomain base.quotientDomain base.dust base.anchor hG hU hdisj hBU hB hTD hE hEU
    π hπ hclosed hsurj hr hbad hinf (fun i => (L i).data)
    (fun i => (L i).physical_eq) (fun i => (L i).quotient_eq)
    (fun i => (L i).dust_eq) (fun i => (L i).anchor_eq)
    (fun i => (L i).domain_agrees) (fun i => ⟨(L i).target_dust, hfinite i⟩) hinj
    (fun i => (L i).law) (fun i => (L i).density) (fun i => (L i).density_measurable)
    (fun i => (L i).occupation_eq) (fun i => (L i).density_energy_finite)
    (fun i => (L i).hit_square_finite)
  intro i j hij
  obtain ⟨n, hn⟩ := hprior i j hij
  exact (L i).ranked_countable_contacts rank hrank (L j) hB hflags hH hweights hmarked hcompat hunique n hn


theorem ranked_countable_endpoints_of_recursive_selection
    {R : Type*} [LinearOrder R] (rank : ℕ → R) (hrank : Injective rank)
    (hcross : UnitDiskAlternatingContinua)
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdisj : Disjoint base.quotientDomain base.dust) (hBU : base.dustᶜ ⊆ base.quotientDomain)
    (hB : IsClosed base.dust) (hTD : IsTotallyDisconnected base.dust)
    (hE : IsClosed base.anchor) (hEU : base.anchor ⊆ base.quotientDomain)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hbad : ∀ x ∈ base.physicalDomainᶜ, π x ∈ base.dust)
    (hinf : π OnePoint.infty ∉ base.dust)
    (flags : Set Sphere) (hflags : flags.Countable)
    (hH : ∀ i, IsClosed (base.levels i))
    (hweights : ∀ i, (∑' x, base.levelWeights i x ^ 2) < ∞)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ flags)
    (hcompat : RankedLevelNullCompatibility rank base.levels (base.dust \ flags))
    (hunique : ∀ x ∈ base.dust \ flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (S : Set Sphere) (hS : S ⊆ base.dust \ {OnePoint.infty})
    (hselect : ∀ (p : Sphere), p ∈ S → ∀ (μ : ℕ → Measure C(PathTime, Sphere)),
      (∀ n, IsFiniteMeasure (μ n)) →
      (∀ n, (support (priorHitMass (μ n))).Countable) →
      ∃ L : RecursiveCodeLaw base π flags ω,
        L.data.target = p ∧ L.data.priorLaws = μ) : S.Countable := by
  by_contra hunc
  obtain ⟨p, hp, hpS⟩ := exists_injective_firstUncountable S hunc
  obtain ⟨L, htarget, hprior⟩ := exists_recursive_code_laws base π flags ω p
    (fun L => L.full_hit_support_countable hU hG hBU hdisj hπ hclosed hsurj hr)
    (fun i μ hf hμ => hselect (p i) (hpS (mem_range_self i)) μ hf hμ)
  have hc : Countable FirstUncountable := ranked_countable_recursive_code_laws rank hrank
    hcross hcoarea hsard hsch base π hG hU hdisj hBU hB hTD hE hEU
    hπ hclosed hsurj hr hbad hinf flags hflags hH hweights hmarked hcompat hunique ω L
    (fun i => by rw [htarget i]; exact (hS (hpS (mem_range_self i))).2)
    (by intro i j hij; apply hp; simpa only [htarget] using hij) hprior
  exact firstUncountable_not_countable hc


theorem ranked_countable_unavailable_endpoints_for_levels
    {R : Type*} [LinearOrder R] (rank : ℕ → R) (hrank : Injective rank)
    (hcross : UnitDiskAlternatingContinua)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀ x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (P : Set Sphere) (hPB : P ⊆ d.dust)
    {g₀ : ℂ → ℝ≥0∞}
    (D : ∀ p : P, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
    (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
    (hshrink : ∀ p : P, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
      ∀ n ≥ k, closure (D p n).region ⊆ V)
    (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : PriorLevelFamily d.physicalDomain π)
    (hlevels : ∀ i, d.levels i = Prod.swap ⁻¹'
      previous.graph i)
    (hweights : ∀ i, (∑' x, d.levelWeights i x ^ 2) < ∞)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (flags : Set Sphere) (hflags : flags.Countable) (hflagsB : flags ⊆ d.dust)
    (hmarked : ∀ i, support (d.levelWeights i) ⊆ flags)
    (hcompat : RankedLevelNullCompatibility rank d.levels (d.dust \ flags))
    (hunique : ∀ x ∈ d.dust \ flags, ∀ i t u,
      (t, x) ∈ d.levels i → (u, x) ∈ d.levels i → t = u)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (β : ℝ≥0∞) (hβ : 0 < β)
    (hno : ∀ p : P, ∀ R : CompatibleLevelBarrier d π previous flags EStar
      (fun j => (D p j).region) (fun _ => ((0 : ℂ) : Sphere)) univ,
      β ≤ R.controlledSize) : P.Countable := by
  obtain ⟨r, hrpos, hrbound⟩ := exists_positive_barrier_duality_parameter C hβ
  have hH (i : ℕ) : IsClosed (d.levels i) := by
    rw [hlevels i]
    exact (previous.closed i).preimage continuous_swap
  let : IsFiniteMeasure (tupleReference ω) := finite_tupleReference hωsum
  have hsmall : (P \ {OnePoint.infty}).Countable := by
    apply ranked_countable_endpoints_of_recursive_selection rank hrank hcross hcoarea hsard hsch
      d π hG hU hdisj hBU hB hTD hE hEU hπ hclosed hsurj hr hbad hinfty
      flags hflags hH hweights hmarked hcompat hunique ω (P \ {OnePoint.infty})
      (fun _ hx => ⟨hPB hx.1, hx.2⟩)
    intro p hp μ hfinite hμ
    let p' : P := ⟨p, hp.1⟩
    let R := Classical.choice (nonempty_priorLawPresentation d.dust flags μ hflags hflagsB hμ)
    let G := RecursiveCodeGeometry.of_presentation d π he p (hPB hp.1) R
      (fun j => frontier (D p' j).region) (fun _ => d.quotientDomain)
    let e := G.data
    let prev : PriorLevelFamily e.physicalDomain π := previous
    let : ∀ n, IsFiniteMeasure (e.priorLaws n) := hfinite
    let : Countable R.marks := R.marks_countable.to_subtype
    have hgate : ∀ i, e.gateContours i ⊆ e.gateSets i := by
      intro i
      exact (D p' i).frontier_region_subset_quotient d π hπ he
        ((D p' i).isOpen_region hπ hclosed hsurj hr)
    let : StandardBorelSpace (BasePathCode e) := standardBorel_basePathCode_of_vacuous_gates
      e hU hB hH hμ (fun i => hflags.mono (hmarked i)) hE.measurableSet hgate
    have hno' (Q : CompatibleLevelBarrier e π prev flags EStar
        (fun j => (D p' j).region) (fun _ => ((0 : ℂ) : Sphere)) univ) :
        β ≤ Q.controlledSize := by
      have hb := hno p' (Q.rebase rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl))
      change β ≤ Q.controlledSize at hb
      exact hb
    obtain ⟨Q, hQ, htest, hcount⟩ := positive_code_law_of_no_small_level_barrier
      hcoarea hLusin hsard hsch e hU hG hdisj π hπ hclosed hsurj hr he
      hB hTD hBU hdense hinfty hbad hinf EStar hE hEU hEStar hEStarE hinfE
      p (hPB hp.1) (fun h => hinfty (h ▸ hPB hp.1)) (D p') (hnest p') (hshrink p')
      (hED p') (fun _ => ((0 : ℂ) : Sphere)) continuous_const
      univ univ isClosed_univ isOpen_univ (Subset.rfl) hfiber harcs prev hlevels
      (fun i => (hweights i).ne) hpoint flags hflags C hC hderiv rfl rfl
      (by ext i x; simp [e, G, RecursiveCodeGeometry.of_presentation, endpointCodeData])
      (fun x : R.marks => x.val) Subtype.val_injective
      (by rintro _ ⟨x, rfl⟩; exact R.marks_dust x.property)
      (hstandard e) hpath ω hω hωsum β hno' (hdual e) (hlift e)
      r hrpos hrbound hunique (by norm_num : (0 : ℝ) < 1)
    exact ⟨RecursiveCodeLaw.of_positive_candidate G ω r hrpos 1 Q hQ htest hcount, rfl, rfl⟩
  apply ((hsmall.insert OnePoint.infty)).mono
  intro p hp
  by_cases hi : p = OnePoint.infty
  · exact Or.inl hi
  · exact Or.inr ⟨hp, hi⟩

end CircleDomainRigidity

end

end OAI
