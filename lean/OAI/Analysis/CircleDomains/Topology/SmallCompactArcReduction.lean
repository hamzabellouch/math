import OAI.Analysis.CircleDomains.Modulus.ArcReductionNormBounds
import OAI.Analysis.CircleDomains.Topology.CompactReductionIntersections

namespace OAI

/-! Every sufficiently deep prescribed collar supports the actual compact
simple-arc law with arbitrarily small density and punctured hit norms. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem eventually_exists_small_compact_arc_law_with_selection
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
    (hb : d.target ∈ d.dust) (htarget : d.target ∉ d.quotientDomain)
    (hhit : (∑' s : d.dust, pathHitProbability (codePathLaw d P) s.val ^ 2) < ∞)
    (V : ℕ → Set Sphere) (hV : ∀ n, IsOpen (V n))
    (hanchor : ∀ n, Disjoint d.anchor (V n)) (hbV : ∀ n, d.target ∈ V n)
    (hanti : Antitone V) (hshrink : (⋂ n, closure (V n)) ⊆ {d.target})
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∃ (K : Set C(PathTime, Sphere)) (η : ProbabilityMeasure C(PathTime, Sphere))
        (gη : Sphere → ℝ≥0∞),
        IsCompact K ∧
        (∀ α ∈ K, α ∈ terminalArcSet (V n) d.target ∧
          physicalDomainLength d.domainEquiv d.basePoint α < ∞) ∧
        (∀ᵐ α ∂(η : Measure C(PathTime, Sphere)), α ∈ K) ∧
        Measurable gη ∧ meanPhysicalOccupation d.domainEquiv d.basePoint η = σ.withDensity gη ∧
        (gη ≤ᵐ[σ] fun x => 2 * (π ⁻¹' V n ∩ d.physicalDomain).indicator g x) ∧
        (∀ x, pathHitProbability η x ≤ 2 * pathHitProbability (codePathLaw d P) x) ∧
        (∀ x ∉ closure (V n), pathHitProbability η x = 0) ∧
        (∫⁻ x, gη x ^ 2 ∂σ) ^ (1 / 2 : ℝ) +
          countingSquareNorm (fun s : d.dust =>
            if s ≠ ⟨d.target, hb⟩ then pathHitProbability η s.val else 0) < ε ∧
        (∀ H : Set Sphere, IsClosed H →
          (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, Sphere))) ≤
            2 * ∫⁻ γ, pathImageCount H γ ∂(codePathLaw d P : Measure C(PathTime, Sphere))) ∧
        IsSubarcLawReduction (codePathLaw d P) η := by
  let A : ℕ → Set Sphere := fun n => π ⁻¹' V n ∩ d.physicalDomain
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (hπ.measurable (hV n).measurableSet).inter hG.measurableSet
  have hAa : Antitone A := fun i j hij x hx => ⟨hanti hij hx.1, hx.2⟩
  have hAi : (⋂ n, A n) ⊆ d.physicalDomainᶜ := by
    intro x hx hxG
    have hpx : π x = d.target := hshrink (mem_iInter.mpr fun n =>
      subset_closure (mem_iInter.mp hx n).1)
    have hu : π x ∈ d.quotientDomain := by
      rw [he ⟨x, hxG⟩]
      exact (d.domainEquiv ⟨x, hxG⟩).property
    exact htarget (hpx ▸ hu)
  have hE := tendsto_shrinking_occupation_energy d hU hG P σ g hg hocc henergy A hAm hAa hAi
  have hgNorm : Tendsto (fun n => (∫⁻ x in A n, g x ^ 2 ∂σ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
      (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hE
  let W : ℕ → Set d.dust := fun n => {s | s.val ∈ closure (V n)}
  have hWa : Antitone (fun n => closure (V n)) := fun i j hij => closure_mono (hanti hij)
  have hW : ∀ s : d.dust, s ≠ ⟨d.target, hb⟩ → ∀ᶠ n in atTop, s ∉ W n := by
    intro s hs
    exact eventually_outside_shrinking_set (fun n => closure (V n)) hWa d.target hshrink
      s.val (fun h => hs (Subtype.ext h))
  have hmNorm := tendsto_punctured_hit_norm_of_finite_tsum
    (fun s : d.dust => pathHitProbability (codePathLaw d P) s.val) hhit.ne
    ⟨d.target, hb⟩ W hW
  have hsum := (ENNReal.Tendsto.const_mul hgNorm (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ∞))).add
    (ENNReal.Tendsto.const_mul hmNorm (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ∞)))
  simp only [mul_zero, add_zero] at hsum
  filter_upwards [hsum.eventually (gt_mem_nhds hε)] with n hn
  obtain ⟨K, η, gη, hK, hKS, hη, hgm, hgmean, hgl, hhi, hho, hcounts, hsel⟩ :=
    exists_compact_arc_reduction_with_selection hselect harcs d hU hG π hπ he P σ g hg hocc henergy
      (V n) (hV n) (hanchor n) (hbV n)
  refine ⟨K, η, gη, hK, hKS, hη, hgm, hgmean, hgl, hhi, hho, ?_, hcounts, hsel⟩
  have hN : countingSquareNorm (fun s : d.dust =>
      if s ≠ ⟨d.target, hb⟩ then pathHitProbability η s.val else 0) ≤
      2 * countingSquareNorm (fun s : d.dust =>
        if s ∈ W n ∧ s ≠ ⟨d.target, hb⟩ then pathHitProbability (codePathLaw d P) s.val else 0) := by
    convert arc_hit_squareNorm_le _ _ ⟨d.target, hb⟩ (W n)
      (fun s => hhi s.val) (fun s hs => hho s.val hs) using 2 <;>
      (congr 1; funext s; split_ifs <;> rfl)
  apply lt_of_le_of_lt (add_le_add (arc_density_squareNorm_le σ g gη hg (A n) (hAm n) hgl) hN)
  convert hn using 2
  congr 2
  funext s
  split_ifs <;> rfl

theorem eventually_exists_small_compact_arc_law
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
    (hb : d.target ∈ d.dust) (htarget : d.target ∉ d.quotientDomain)
    (hhit : (∑' s : d.dust, pathHitProbability (codePathLaw d P) s.val ^ 2) < ∞)
    (V : ℕ → Set Sphere) (hV : ∀ n, IsOpen (V n))
    (hanchor : ∀ n, Disjoint d.anchor (V n)) (hbV : ∀ n, d.target ∈ V n)
    (hanti : Antitone V) (hshrink : (⋂ n, closure (V n)) ⊆ {d.target})
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∃ (K : Set C(PathTime, Sphere)) (η : ProbabilityMeasure C(PathTime, Sphere))
        (gη : Sphere → ℝ≥0∞),
        IsCompact K ∧
        (∀ α ∈ K, α ∈ terminalArcSet (V n) d.target ∧
          physicalDomainLength d.domainEquiv d.basePoint α < ∞) ∧
        (∀ᵐ α ∂(η : Measure C(PathTime, Sphere)), α ∈ K) ∧
        Measurable gη ∧ meanPhysicalOccupation d.domainEquiv d.basePoint η = σ.withDensity gη ∧
        (gη ≤ᵐ[σ] fun x => 2 * (π ⁻¹' V n ∩ d.physicalDomain).indicator g x) ∧
        (∀ x, pathHitProbability η x ≤ 2 * pathHitProbability (codePathLaw d P) x) ∧
        (∀ x ∉ closure (V n), pathHitProbability η x = 0) ∧
        (∫⁻ x, gη x ^ 2 ∂σ) ^ (1 / 2 : ℝ) +
          countingSquareNorm (fun s : d.dust =>
            if s ≠ ⟨d.target, hb⟩ then pathHitProbability η s.val else 0) < ε ∧
        ∀ H : Set Sphere, IsClosed H →
          (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, Sphere))) ≤
            2 * ∫⁻ γ, pathImageCount H γ ∂(codePathLaw d P : Measure C(PathTime, Sphere)) := by
  filter_upwards [eventually_exists_small_compact_arc_law_with_selection hselect harcs d hU hG
    π hπ he P σ g hg hocc henergy hb htarget hhit V hV hanchor hbV hanti hshrink hε] with n hn
  obtain ⟨K, η, gη, hK, hKS, hη, hgm, hgmean, hgl, hhi, hho, hnorm, hcounts, _⟩ := hn
  exact ⟨K, η, gη, hK, hKS, hη, hgm, hgmean, hgl, hhi, hho, hnorm, hcounts⟩

end CircleDomainRigidity

end

end OAI
