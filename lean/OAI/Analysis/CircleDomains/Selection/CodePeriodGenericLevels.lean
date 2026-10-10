import OAI.Analysis.CircleDomains.Rigidity.CodePeriodFreeTrace
import OAI.Analysis.CircleDomains.Selection.PeriodDomainIntersections
import OAI.Analysis.CircleDomains.Selection.PeriodDomainValues
import OAI.Analysis.CircleDomains.Selection.MeanLevelAssembly
import OAI.Analysis.CircleDomains.Probability.LevelLawQuantifiers

namespace OAI

/-! The period-coordinate case of the generic prior-level theorem.
Local branches supply null free traces; intrinsic two-cut coarea controls
physical counts, and the actual dust budget controls flagged counts. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem code_period_generic_levels
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
    (hP : OrderedLevelNullCompatibility d.levels (d.quotientDomainᶜ \ Flags))
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
  have hfree := ae_code_period_free_level_incidence_null hsard hsch d hG hU hdense hdust
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
