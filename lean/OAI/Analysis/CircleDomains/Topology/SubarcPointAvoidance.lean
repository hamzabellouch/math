import OAI.Analysis.CircleDomains.Topology.SubarcIntersectionCount
import OAI.Analysis.CircleDomains.Probability.RecursiveCodeLaw

namespace OAI

/-! Point avoidance outside the original law's positive-hit set survives
the actual subarc selector and compact conditioning. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem IsSubarcLawReduction.avoids_point
    {μ ν : ProbabilityMeasure C(PathTime, Sphere)} (hred : IsSubarcLawReduction μ ν)
    {x : Sphere} (hx : pathHitProbability μ x = 0) :
    ∀ᵐ γ : C(PathTime, Sphere) ∂(ν : Measure C(PathTime, Sphere)), x ∉ range γ := by
  obtain ⟨f, hf, hs, hν⟩ := hred
  have hμ : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)), x ∉ range γ := by
    apply ae_iff.mpr
    simpa only [not_not, mem_range, pathHitProbability] using hx
  have hsel : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      x ∉ range (f γ) := by
    filter_upwards [hμ, hs] with γ hγ hsub
    exact fun hx => hγ (hsub hx)
  have hmap : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ.map f : Measure C(PathTime, Sphere)),
      x ∉ range γ := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff hf ?_).mpr hsel
    exact (isClosed_paths_hitting x).isOpen_compl.measurableSet
  exact (Measure.absolutelyContinuous_of_le_smul hν).ae_le hmap

 theorem RecursiveCodeLaw.subarc_avoids_unmarked_point
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    (L : RecursiveCodeLaw base π Flags ω)
    (T : Set Sphere)
    (hT : {x | x ∈ L.data.dust ∧ 0 < codeHitProbability L.data L.law x} ⊆ T)
    {ν : ProbabilityMeasure C(PathTime, Sphere)}
    (hred : IsSubarcLawReduction (codePathLaw L.data L.law) ν)
    {A : Set C(PathTime, Sphere)} (η : ProbabilityMeasure A) (hη : η.map Subtype.val = ν)
    {x : Sphere} (hx : x ∈ base.dust \ T) :
    ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val := by
  have hz : pathHitProbability (codePathLaw L.data L.law) x = 0 := by
    rw [pathHitProbability_codePathLaw]
    by_contra hn
    exact hx.2 (hT ⟨L.dust_eq.symm ▸ hx.1, pos_iff_ne_zero.mpr hn⟩)
  have hν := hred.avoids_point hz
  rw [← hη, ProbabilityMeasure.toMeasure_map] at hν
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable hν

def RecursiveCodeLaw.extendedHitFlags
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞} (L : RecursiveCodeLaw base π Flags ω) :
    Set Sphere := Flags ∪ {x | x ∈ L.data.dust ∧ 0 < codeHitProbability L.data L.law x}

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem RecursiveCodeLaw.extendedHitFlags_countable
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞} (L : RecursiveCodeLaw base π Flags ω)
    (hFlags : Flags.Countable) : L.extendedHitFlags.Countable :=
  hFlags.union L.countable_dust_hits

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem RecursiveCodeLaw.extendedHitFlags_subset
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞} (L : RecursiveCodeLaw base π Flags ω)
    (hFlags : Flags ⊆ base.dust) : L.extendedHitFlags ⊆ base.dust := by
  intro x hx
  rcases hx with hx | hx
  · exact hFlags hx
  · exact L.dust_eq ▸ hx.1

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem RecursiveCodeLaw.target_mem_extendedHitFlags
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞} (L : RecursiveCodeLaw base π Flags ω) :
    L.data.target ∈ L.extendedHitFlags := by
  right
  refine ⟨L.dust_eq.symm ▸ L.target_dust, ?_⟩
  have heq : {Γ : BasePathCode L.data | L.data.target ∈ range Γ.val.1} = univ := by
    apply eq_univ_of_forall
    intro Γ
    exact ⟨⊤, Γ.property.2.1.2.1⟩
  change 0 < (L.law : Measure (BasePathCode L.data)) _
  rw [heq, measure_univ]
  norm_num

end CircleDomainRigidity

end

end OAI
