import OAI.Analysis.CircleDomains.Selection.RebasedLevelPresentations
import OAI.Analysis.CircleDomains.Selection.PresentedPriorLevels
import OAI.Analysis.CircleDomains.Probability.RecursiveCodeLaw

namespace OAI

/-! A recursively selected positive law supplies the visit and deletion
estimates required by all earlier real and mean levels. No generic-level
assumption remains in this application. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem RecursiveCodeLaw.generic_prior_levels
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
    (L : RecursiveCodeLaw base π Flags ω) :
    ∀ i, ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, θ) ∈ (C i).graph} γ
        ∂(codePathLaw L.data L.law : Measure C(PathTime, Sphere))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, Sphere) ∂(codePathLaw L.data L.law : Measure C(PathTime, Sphere)),
        ¬ ∃ x ∈ range γ ∩ (base.quotientDomainᶜ \ Flags), (x, θ) ∈ (C i).graph := by
  let D (i : ℕ) := (C i).rebaseDust L.physical_eq L.quotient_eq L.dust_eq
  have hpres (i : ℕ) : SelectedLevelPresentation hsch L.data π (D i) :=
    (presentation i).rebase L.physical_eq L.quotient_eq L.dust_eq
  have hlev (i : ℕ) : L.data.levels i = Prod.swap ⁻¹' (D i).graph := by
    rw [L.levels_eq, hlevel i]
    exact congrArg (fun T => Prod.swap ⁻¹' T)
      ((C i).graph_rebaseDust L.physical_eq L.quotient_eq L.dust_eq).symm
  have hwgt (i : ℕ) : L.data.levelWeights i = (D i).dustWeight := by
    rw [L.weights_eq, hweights i]
    exact ((C i).dustWeight_rebaseDust L.physical_eq L.quotient_eq L.dust_eq).symm
  have hm (i : ℕ) : support (L.data.levelWeights i) ⊆ Flags := by
    rw [L.weights_eq]
    exact hmarked i
  have hs (i : ℕ) : ((D i).singular : Sphere) ∈ Flags := by
    rw [(C i).singular_rebaseDust]
    exact hsingular i
  have hv (i : ℕ) : countingSquareNorm (fun x : support (L.data.levelWeights i) =>
      meanVisitCount (codePathLaw L.data L.law) x.val) < ∞ := by
    rw [L.weights_eq]
    exact L.flag_visit_norm_finite i (hmarked i)
  have hc : ∀ i x, x ∈ support (L.data.levelWeights i) →
      ∀ᶠ n in atTop, x ∈ L.data.flagDeletions n := by
    intro i x hx
    rw [L.weights_eq] at hx
    simpa only [L.flag_deletions_eq] using L.presentation.flag_cover x (hmarked i hx)
  have hd : ∀ n, (L.data.flagDeletions n : Set Sphere) ⊆ Flags := by
    intro n
    simpa only [L.flag_deletions_eq] using L.presentation.flag_subset n
  have hg := presented_prior_generic_levels rank hrank hcoarea hsard hsch hsep L.data
    (by simpa only [L.physical_eq] using hG)
    (by simpa only [L.quotient_eq] using hU)
    (by simpa only [L.quotient_eq] using hdense)
    (by simpa only [L.dust_eq, L.quotient_eq] using hdust)
    π hπ hclosed hsurj (by simpa only [L.physical_eq] using hr) L.domain_agrees
    (by simpa only [L.quotient_eq] using hTD)
    (by simpa only [L.physical_eq, L.quotient_eq] using hbad)
    Flags hFlags (by simpa only [L.quotient_eq] using hFlagsB)
    L.law L.density L.density_measurable L.occupation_eq L.density_energy_finite D hpres hlev hwgt
    hm hs hv hc hd (by simpa only [L.levels_eq, L.quotient_eq] using hP)
    (by simpa only [L.levels_eq, L.quotient_eq] using hunique)
    ω L.tuple_absolutelyContinuous
  simpa only [D, MaskedCoordinateData.graph_rebaseDust, L.quotient_eq] using hg

end CircleDomainRigidity

end

end OAI
