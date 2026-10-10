import OAI.Analysis.CircleDomains.Probability.RecursiveCodeLaw
import OAI.Analysis.CircleDomains.Topology.SmallCompactArcReduction
import OAI.Analysis.CircleDomains.Probability.SupportedProbability
import OAI.Analysis.CircleDomains.Topology.SubarcGates

namespace OAI

/-! The recursive positive law gives an actual compactly supported terminal-arc law at
sufficiently deep collars. Its physical density and punctured hit norm are arbitrarily
small, and the original prescribed gates survive the reduction. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

structure CompactRecursiveReduction
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    (L : RecursiveCodeLaw base π Flags ω) (V : Set Sphere) (ε : ℝ≥0∞) where
  arcs : Set C(PathTime, Sphere)
  compact : IsCompact arcs
  terminal : arcs ⊆ terminalArcSet V L.data.target
  finite_length : ∀ γ ∈ arcs, physicalDomainLength L.data.domainEquiv L.data.basePoint γ < ∞
  law : ProbabilityMeasure arcs
  density : Sphere → ℝ≥0∞
  density_measurable : Measurable density
  occupation : meanPhysicalOccupation L.data.domainEquiv L.data.basePoint (law.map Subtype.val) =
    sphericalArea.withDensity density
  hit_le : ∀ x, pathHitProbability (law.map Subtype.val) x ≤
    2 * pathHitProbability (codePathLaw L.data L.law) x
  outside : ∀ x ∉ closure V, pathHitProbability (law.map Subtype.val) x = 0
  small : (∫⁻ x, density x ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) +
    countingSquareNorm (fun s : L.data.dust =>
      if s.val ≠ L.data.target then pathHitProbability (law.map Subtype.val) s.val else 0) < ε
  reduction : IsSubarcLawReduction (codePathLaw L.data L.law) (law.map Subtype.val)

 theorem RecursiveCodeLaw.eventually_compact_reduction
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    (L : RecursiveCodeLaw base π Flags ω)
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hU : IsOpen base.quotientDomain) (hG : IsOpen base.physicalDomain)
    (hπ : Continuous π) (hdisj : Disjoint base.quotientDomain base.dust)
    (V : ℕ → Set Sphere) (hV : ∀ n, IsOpen (V n))
    (hanchor : ∀ n, Disjoint base.anchor (V n)) (hbV : ∀ n, L.data.target ∈ V n)
    (hanti : Antitone V) (hshrink : (⋂ n, closure (V n)) ⊆ {L.data.target})
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n in atTop, Nonempty (CompactRecursiveReduction L (V n) ε) := by
  have hb : L.data.target ∈ L.data.dust := L.dust_eq.symm ▸ L.target_dust
  have hout : L.data.target ∉ L.data.quotientDomain := by
    intro h
    exact disjoint_left.mp hdisj (L.quotient_eq ▸ h) L.target_dust
  have hhit : (∑' s : L.data.dust, pathHitProbability (codePathLaw L.data L.law) s.val ^ 2) < ∞ := by
    rw [L.dust_eq]
    simpa only [pathHitProbability_codePathLaw] using L.hit_square_finite
  filter_upwards [eventually_exists_small_compact_arc_law_with_selection hselect harcs L.data
    (L.quotient_eq.symm ▸ hU) (L.physical_eq.symm ▸ hG) π hπ
    (fun y => (L.domain_agrees y).symm) L.law sphericalArea L.density L.density_measurable
    L.occupation_eq L.density_energy_finite hb hout hhit V hV
    (fun n => L.anchor_eq.symm ▸ hanchor n) hbV hanti hshrink hε] with n hn
  obtain ⟨K, ν, g, hK, hterminal, hν, hg, hocc, _, hhitν, houtν, hsmall, _, hred⟩ := hn
  let η := supportedProbability ν K hK.measurableSet hν
  have hη : η.map Subtype.val = ν := supportedProbability_map ν K hK.measurableSet hν
  refine ⟨{
    arcs := K
    compact := hK
    terminal := fun _ h => (hterminal _ h).1
    finite_length := fun _ h => (hterminal _ h).2
    law := η
    density := g
    density_measurable := hg
    occupation := by rw [hη]; exact hocc
    hit_le := by rw [hη]; exact hhitν
    outside := by rw [hη]; exact houtν
    small := ?_
    reduction := by rw [hη]; exact hred }⟩
  rw [hη]
  convert hsmall using 2
  congr 1
  funext s
  have hs : s ≠ (⟨L.data.target, hb⟩ : L.data.dust) ↔ s.val ≠ L.data.target := by
    simp only [ne_eq, Subtype.ext_iff]
  simp only [hs]

 theorem CompactRecursiveReduction.start_gate
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    {L : RecursiveCodeLaw base π Flags ω} {V : Set Sphere} {ε : ℝ≥0∞}
    (Q : CompactRecursiveReduction L V ε)
    (hC : ∀ n, IsClosed (L.data.gateContours n)) (hK : ∀ n, IsClosed (L.data.gateSets n))
    (n : ℕ) (hfront : frontier V ⊆ L.data.gateContours n) :
    ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs), γ.val ⊥ ∈ L.data.gateSets n := by
  have hgate := Q.reduction.code_gates L.data L.law hC hK
  rw [ProbabilityMeasure.toMeasure_map] at hgate
  have hg := ae_of_ae_map measurable_subtype_coe.aemeasurable hgate
  filter_upwards [hg] with γ hγ
  exact hγ n ⊥ (hfront (Q.terminal γ.property).2.1)

end CircleDomainRigidity

end

end OAI
