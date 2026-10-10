import OAI.Analysis.CircleDomains.Probability.SelectableMeanLaw
import OAI.Analysis.CircleDomains.Selection.RecursiveMeanExclusion

namespace OAI

/-! The constructed recursive mean is compatible with the actual preceding
selected presentations. Its physical coordinate and open exclusion are retained. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem RecursiveMeanOutput.selectable
    {O : Type*} [LinearOrder O] (rank : ℕ → O) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ base.quotientDomainᶜ)
    (C : ℕ → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val))
    (presentation : ∀ i, SelectedLevelPresentation hsch base π (C i))
    (hlevel : ∀ i, base.levels i = Prod.swap ⁻¹' (C i).graph)
    (hweights : ∀ i, base.levelWeights i = (C i).dustWeight)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ Flags)
    (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
    (hP : RankedLevelNullCompatibility rank base.levels (base.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (L : RecursiveCodeLaw base π Flags ω)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ D : Set Sphere, IsCompact D → LocallyConnectedSpace D →
      HasSimpleArcsInConnectedOpens D)
    (previous : PriorLevelFamily base.physicalDomain π)
    (hprevious : ∀ i, previous.graph i = (C i).graph)
    {J : ℂ ≃ₜ ℂ} {ε : ℝ≥0∞}
    (Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J) ε)
    {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)}
    {c₀ : ℂ} {r₀ : ℝ≥0} {R₀ δ : ℝ}
    (R : RecursiveMeanOutput hsch Q F₀ hF₀ c₀ r₀ R₀ δ)
    (hbJ : L.data.target ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (hweighted : WeightedPlanarScalarCoarea)
    (hebase : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (Candidates : Set (SelectableMaskedCoordinate base π))
    (label : SelectableMaskedCoordinate base π → ℕ)
    (hflags : ∀ c ∈ Candidates, c.flags ⊆ L.extendedHitFlags)
    (hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c)) :
    ∃ c : SelectableMaskedCoordinate base π, c.coordinate = R.coordinate ∧
      c.CompatibleWith Candidates ∧
      Nonempty (MeanCoordinatePresentation hsch base π c.coordinate) ∧
      c.coordinate.sourceStokesBudget R₀ < δ ∧
      Nonempty (MeanExclusionWitness c.coordinate F₀ hF₀ c₀ r₀ R₀) := by
  have hExt : L.extendedHitFlags ⊆ base.quotientDomainᶜ := by
    rw [← hdust]
    exact L.extendedHitFlags_subset (fun x hx => hdust.symm ▸ hFlagsB hx)
  have hboundary : R.mask \ interior R.mask ⊆ base.quotientDomain := by
    intro x hx
    apply R.frontier
    rw [_root_.frontier, R.closed.closure_eq]
    exact hx
  have hMS : R.mask \ {L.data.target} ⊆ R.centered.punctured :=
    fun _ hx => ⟨R.inner hx.1, hx.2⟩
  obtain ⟨c, hc, hcomp, hpres⟩ := L.selectable_mean_coordinate rank hrank hcoarea hsard hsch hsep
    base hG hU hdense hdust π hπ hclosed hsurj hr hTD hbad
    Flags hFlags hFlagsB C presentation hlevel hweights hmarked hsingular hP hunique ω
    hLusin hfiber harcs previous hprevious
    L.extendedHitFlags (L.extendedHitFlags_countable hFlags) hExt (fun _ hx => Or.inl hx)
    R.centered.punctured R.mask L.data.target L.target_mem_extendedHitFlags
    (fun h => h.2 rfl) hboundary hMS Q.arcs R.centered.diskArcs R.centered.compact
    R.centered.terminal Q.law R.centered.map R.centered.arcMap
    R.centered.continuous_arcMap.measurable R.centered.arcMap_eq
    (Q.law.map Subtype.val) Q.reduction rfl (R.centered.nonzero hbJ)
    (R.centered.norm_le hbJ) (R.centered.injective_arcs hbJ Q.terminal)
    (R.centered.injective_punctured hbJ) (fun _ hx => Or.inr hx)
    R.mean hweighted hebase (fun x hx => R.centered.norm_lt hbJ x (R.inner hx.1))
    R.centered.punctured_open R.closed R.infty_not_mem R.target_mem
    R.coordinate R.graph R.singular_eq Candidates label hflags hgraphs

  refine ⟨c, hc, hcomp, hpres, ?_, ?_⟩
  · rw [hc]
    exact R.budget
  · rw [hc]
    exact ⟨R.exclusion⟩

end CircleDomainRigidity

end

end OAI
