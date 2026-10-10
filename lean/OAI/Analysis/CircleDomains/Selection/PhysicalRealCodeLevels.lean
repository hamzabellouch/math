import OAI.Analysis.CircleDomains.Selection.RankedRealCodeLevels
import OAI.Analysis.CircleDomains.Probability.ExactBandMeasure
import OAI.Analysis.CircleDomains.Sobolev.PhysicalCoordinateCoarea

namespace OAI

/-! Real seed coordinates retain the same code-law intersection estimates
when interspersed with masked period coordinates in an inherited order. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem PhysicalRealCoordinate.ranked_code_generic_levels
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
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hcover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (Q : PhysicalRealCoordinate d π)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (hgraph : C.graph = circleBandGraph d.quotientDomain Q.quotient)
    (hlevel : d.levels i = Prod.swap ⁻¹' C.graph)
    (hweights : d.levelWeights i = C.dustWeight)
    {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ d.physicalDomain → z ∉ K → Q.quotient (π (z : Sphere)) = 0)
    (hinfty : OnePoint.infty ∈ d.physicalDomain → Q.quotient (π OnePoint.infty) = 0) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ Γ : BasePathCode d, pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1
        ∂(P : Measure _)) < ∞ ∧
      ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        ¬ ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
  let D := ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain
  let e := Complex.equivRealProdCLM
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hDc : D = e ⁻¹' realChartDomain d.physicalDomain := by
    ext z
    change (z : Sphere) ∈ d.physicalDomain ↔ (e.symm (e z) : Sphere) ∈ d.physicalDomain
    rw [e.symm_apply_apply]
  have hreal : IsOpen (realChartDomain d.physicalDomain) :=
    hG.preimage (OnePoint.continuous_coe.comp e.symm.continuous)
  have hs : ContDiffOn ℝ 1 Q.physical (realChartDomain d.physicalDomain) :=
    Q.physical_smooth.of_le (by simp)
  have hpc : ContDiffOn ℝ 1 (Q.physical ∘ e) D := by
    rw [hDc]
    exact hs.comp e.contDiff.contDiffOn (fun _ hx => hx)
  have heq : EqOn (fun z : ℂ => Q.quotient (π (z : Sphere))) (Q.physical ∘ e) D :=
    fun z hz => (Q.pullback z hz).symm
  have hv := hpc.congr heq
  have hEn : (∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ (Q.physical ∘ e) z‖ ^ 2)) < ∞ := by
    rw [hDc]
    exact complex_chart_differential_energy_finite hreal hs Q.physical_energy
  have henergy : (∫⁻ z in D, ENNReal.ofReal
      ‖fderiv ℝ (fun z : ℂ => Q.quotient (π (z : Sphere))) z‖ ^ 2) < ∞ := by
    have heD : ∀ᵐ z ∂volume.restrict D,
        fderiv ℝ (fun z : ℂ => Q.quotient (π (z : Sphere))) z =
          fderiv ℝ (Q.physical ∘ e) z := by
      filter_upwards [ae_restrict_mem hD.measurableSet] with z hz
      have hev : (fun y : ℂ => Q.quotient (π (y : Sphere))) =ᶠ[𝓝 z] Q.physical ∘ e :=
        Filter.mem_of_superset (hD.mem_nhds hz) (fun _ hy => heq hy)
      exact hev.fderiv_eq
    have heD' : (∫⁻ z in D, ENNReal.ofReal
        ‖fderiv ℝ (fun z : ℂ => Q.quotient (π (z : Sphere))) z‖ ^ 2) =
        ∫⁻ z in D, ENNReal.ofReal ‖fderiv ℝ (Q.physical ∘ e) z‖ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [heD] with z hz
      rw [hz]
    rw [heD']
    simpa only [ENNReal.ofReal_pow (norm_nonneg _)] using hEn
  have hbound (x : Sphere) (_ : x ∈ d.quotientDomain) : |Q.quotient x| ≤ 1 := by
    rw [abs_of_nonneg (Q.quotient_unit x).1]
    exact (Q.quotient_unit x).2
  have hband (x : Sphere) (hx : x ∈ d.quotientDomainᶜ) :
      ENNReal.ofReal (limsup Q.quotient (𝓝[d.quotientDomain] x) -
        liminf Q.quotient (𝓝[d.quotientDomain] x)) ≤ d.levelWeights i x := by
    have hcl : x ∈ closure d.quotientDomain := by rw [hdense.closure_eq]; trivial
    let : NeBot (𝓝[d.quotientDomain] x) := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have hlo : 0 ≤ liminf Q.quotient (𝓝[d.quotientDomain] x) :=
      le_liminf_of_le (isBoundedUnder_of_eventually_le
        (Eventually.of_forall fun y => (Q.quotient_unit y).2)).isCoboundedUnder_ge
        (Eventually.of_forall fun y => (Q.quotient_unit y).1)
    have hhi : limsup Q.quotient (𝓝[d.quotientDomain] x) ≤ 1 :=
      limsup_le_of_le (isBoundedUnder_of_eventually_ge
        (Eventually.of_forall fun y => (Q.quotient_unit y).1)).isCoboundedUnder_le
        (Eventually.of_forall fun y => (Q.quotient_unit y).2)
    have hxB : x ∈ d.dust := hdust.symm ▸ hx
    rw [hweights, MaskedCoordinateData.dustWeight, dite_eq_left hxB]
    apply band_width_le_of_fiber_subset hbound hcl (by linarith)
    intro θ hθ
    apply C.marked_fiber ⟨x, hxB⟩
    rwa [hgraph]
  exact ranked_code_real_generic_levels rank hrank hcoarea hsard hsch d
    hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB
    Q.quotient hbound Q.quotient_continuous hv henergy hK hzero hinfty P ρ hρ hocc hρ2
    i hm hweight hvisits hband hmFree hcover hdeletions hH hP hunique ω hτ
    (fun θ x => by rw [hlevel, mem_preimage, Prod.swap_prod_mk, hgraph])

end CircleDomainRigidity

end

end OAI
