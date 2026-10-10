import OAI.Analysis.CircleDomains.Topology.CompactArcIntersections
import OAI.Analysis.CircleDomains.Probability.CodeLawPhysicalOccupation
import OAI.Analysis.CircleDomains.Probability.DominatedDensity
import OAI.Analysis.CircleDomains.Sobolev.ShrinkingOccupationEnergy

namespace OAI

/-! Compact simple-arc reduction for the actual endpoint code law, with
its pointwise density bound and all closed-set intersection bounds. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_compact_arc_reduction_with_selection
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    (P : ProbabilityMeasure (BasePathCode d))
    (σ : Measure Sphere) [IsFiniteMeasure σ] (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanCodeOccupation d P = σ.withDensity g)
    (henergy : (∫⁻ x, g x ^ 2 ∂σ) < ∞)
    (V : Set Sphere) (hV : IsOpen V) (hanchor : Disjoint d.anchor V) (hb : d.target ∈ V) :
    ∃ (K : Set C(PathTime, Sphere)) (η : ProbabilityMeasure C(PathTime, Sphere))
      (gη : Sphere → ℝ≥0∞),
      IsCompact K ∧
      (∀ α ∈ K, α ∈ terminalArcSet V d.target ∧
        physicalDomainLength d.domainEquiv d.basePoint α < ∞) ∧
      (∀ᵐ α ∂(η : Measure C(PathTime, Sphere)), α ∈ K) ∧
      Measurable gη ∧ meanPhysicalOccupation d.domainEquiv d.basePoint η = σ.withDensity gη ∧
      (gη ≤ᵐ[σ] fun x => 2 * (π ⁻¹' V ∩ d.physicalDomain).indicator g x) ∧
      (∀ x, pathHitProbability η x ≤ 2 * pathHitProbability (codePathLaw d P) x) ∧
      (∀ x ∉ closure V, pathHitProbability η x = 0) ∧
      (∀ H : Set Sphere, IsClosed H →
        (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, Sphere))) ≤
          2 * ∫⁻ γ, pathImageCount H γ ∂(codePathLaw d P : Measure C(PathTime, Sphere))) ∧
      IsSubarcLawReduction (codePathLaw d P) η := by
  obtain ⟨K, η, hK, hKS, hη, hhit, hout, hbound, hcounts, hsel⟩ :=
    exists_compact_physical_arc_law_with_selection hselect harcs d.domainEquiv hU d.basePoint π hπ he
      (codePathLaw d P) V hV d.target (codePathLaw_collar_endpoints d hU P V hV hanchor hb)
  rw [meanPhysicalOccupation_codePathLaw d hU P, hocc] at hbound
  have hmem : ∀ᵐ x ∂σ.withDensity g, x ∈ d.physicalDomain := by
    rw [ae_iff]
    exact hocc ▸ meanCodeOccupation_compl d hU hG P
  have hset : π ⁻¹' V ∩ d.physicalDomain =ᵐ[σ.withDensity g] π ⁻¹' V := by
    filter_upwards [hmem] with x hx
    simp only [mem_inter_iff, and_iff_left hx]
  have hbound' : meanPhysicalOccupation d.domainEquiv d.basePoint η ≤
      (2 : ℝ≥0∞) • (σ.withDensity g).restrict (π ⁻¹' V ∩ d.physicalDomain) := by
    rwa [Measure.restrict_congr_set hset]
  obtain ⟨gη, hgη, hηg, hle⟩ := exists_localized_density_of_square_domination σ
    (meanPhysicalOccupation d.domainEquiv d.basePoint η) g hg henergy
    (π ⁻¹' V ∩ d.physicalDomain) ((hπ.measurable hV.measurableSet).inter hG.measurableSet) hbound'
  exact ⟨K, η, gη, hK, hKS, hη, hgη, hηg, hle, hhit, hout, hcounts, hsel⟩

theorem exists_compact_arc_reduction_with_intersections
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    (P : ProbabilityMeasure (BasePathCode d))
    (σ : Measure Sphere) [IsFiniteMeasure σ] (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanCodeOccupation d P = σ.withDensity g)
    (henergy : (∫⁻ x, g x ^ 2 ∂σ) < ∞)
    (V : Set Sphere) (hV : IsOpen V) (hanchor : Disjoint d.anchor V) (hb : d.target ∈ V) :
    ∃ (K : Set C(PathTime, Sphere)) (η : ProbabilityMeasure C(PathTime, Sphere))
      (gη : Sphere → ℝ≥0∞),
      IsCompact K ∧
      (∀ α ∈ K, α ∈ terminalArcSet V d.target ∧
        physicalDomainLength d.domainEquiv d.basePoint α < ∞) ∧
      (∀ᵐ α ∂(η : Measure C(PathTime, Sphere)), α ∈ K) ∧
      Measurable gη ∧ meanPhysicalOccupation d.domainEquiv d.basePoint η = σ.withDensity gη ∧
      (gη ≤ᵐ[σ] fun x => 2 * (π ⁻¹' V ∩ d.physicalDomain).indicator g x) ∧
      (∀ x, pathHitProbability η x ≤ 2 * pathHitProbability (codePathLaw d P) x) ∧
      (∀ x ∉ closure V, pathHitProbability η x = 0) ∧
      ∀ H : Set Sphere, IsClosed H →
        (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, Sphere))) ≤
          2 * ∫⁻ γ, pathImageCount H γ ∂(codePathLaw d P : Measure C(PathTime, Sphere)) := by
  obtain ⟨K, η, gη, hK, hKS, hη, hgη, hoccη, hle, hhit, hout, hcounts, _⟩ :=
    exists_compact_arc_reduction_with_selection hselect harcs d hU hG π hπ he P σ g hg
      hocc henergy V hV hanchor hb
  exact ⟨K, η, gη, hK, hKS, hη, hgη, hoccη, hle, hhit, hout, hcounts⟩

end CircleDomainRigidity

end

end OAI
