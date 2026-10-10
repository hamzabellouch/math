import OAI.Analysis.CircleDomains.Selection.SelectedLevelPresentation
import OAI.Analysis.CircleDomains.Probability.CountableLawRestriction
import OAI.Analysis.CircleDomains.Selection.MappedGenericLevels

namespace OAI

/-! The actual countable real/mean presentations give generic prior-level
estimates for the path law. Closedness, square-summable weights, and free
weights are obtained from the stored coordinates and common marks. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem presented_prior_generic_levels
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
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
    (C : ℕ → MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (presentation : ∀ i, SelectedLevelPresentation hsch d π (C i))
    (hlevel : ∀ i, d.levels i = Prod.swap ⁻¹' (C i).graph)
    (hweights : ∀ i, d.levelWeights i = (C i).dustWeight)
    (hmarked : ∀ i, support (d.levelWeights i) ⊆ Flags)
    (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
    (hvisits : ∀ i, countingSquareNorm
      (fun x : support (d.levelWeights i) => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ i x, x ∈ support (d.levelWeights i) → ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω) :
    ∀ i, ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, θ) ∈ (C i).graph} γ
        ∂(codePathLaw d P : Measure C(PathTime, Sphere))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, Sphere) ∂(codePathLaw d P : Measure C(PathTime, Sphere)),
        ¬ ∃ x ∈ range γ ∩ (d.quotientDomainᶜ \ Flags), (x, θ) ∈ (C i).graph := by
  have hH (i : ℕ) : IsClosed (d.levels i) := by
    rw [hlevel i]
    exact (C i).graph_closed.preimage continuous_swap
  have hσU : IsSigmaCompact d.quotientDomain := by
    let : LocallyCompactSpace d.quotientDomain := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  intro i
  have hm : (support (d.levelWeights i)).Countable := hFlags.mono (hmarked i)
  have hw : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞ := by
    apply (countingSquareNorm_comp_injective (d.levelWeights i)
      (fun x : support (d.levelWeights i) => x.val) Subtype.val_injective).trans_lt
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    rw [hweights i]
    exact (C i).dustWeight_square_sum.ne
  have hfree (x : Sphere) (hx : x ∈ d.quotientDomainᶜ \ Flags) : d.levelWeights i x = 0 := by
    by_contra hn
    exact hx.2 (hmarked i hn)
  have hg := (presentation i).generic_levels rank hrank hcoarea hsard hsch d
    hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB P ρ hρ hocc hρ2
    i hm hw (hvisits i) hfree (hcover i) hdeletions hH hP hunique ω hτ hsep
    (C i) (hlevel i) (hweights i) (hsingular i)
  have hdj : Disjoint d.quotientDomain Flags :=
    disjoint_left.mpr (fun x hx hxf => hFlagsB hxf hx)
  have hh := map_generic_levels P (codePath d) (measurable_codePath d) (hH i)
    d.quotientDomain Flags hσU hFlags hdj hg
  simpa only [codePathLaw, hlevel i, mem_preimage, Prod.swap_prod_mk] using hh

end CircleDomainRigidity

end

end OAI
