import OAI.Analysis.CircleDomains.Selection.ProjectedLevelTollZero
import OAI.Analysis.CircleDomains.Modulus.WeightedCollarNeighborhoods

namespace OAI

/-! The actual weighted collars supply the local short joining arcs
required for splicing. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_small_weighted_collar_arcs_of_level_toll_zero
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞)
    {B : Set Sphere} {p : Sphere}
    (D : WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (hm : ∀z : ℂ, D.function z = D.level → m (π (z : Sphere)) = 0)
    (hD : IsOpen D.region) {T : Set Sphere}
    (hlevel : {z | D.function z = D.level} ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' T)
    {x : Sphere} (hx : x ∈ frontier D.region) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Set Sphere, W ∈ 𝓝 x ∧
      ∀a ∈ W ∩ frontier D.region, ∀b ∈ W ∩ frontier D.region,
        ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
          ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧ range ρ.1.val ⊆ T ∧
          physicalTollCost d g m ρ.1 ≤ ε := by
  have hfront := D.frontier_region_subset hπ hD
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hfront hx
  obtain ⟨W, hW, hzW, hsmall⟩ := exists_small_projected_regular_level_arcs_of_level_toll_zero
    d hU hdisj π he ν N D.smooth D.regular
    (fun z hz => (D.level_good z hz).1) g hg D.cost_finite m hm hz hε
  refine ⟨W, hW.mem_nhds hzW, ?_⟩
  intro a ha b hb
  obtain ⟨ρ, hρ, hρ0, hρ1, hρrange, hρcost⟩ :=
    hsmall a ⟨ha.1, hfront ha.2⟩ b ⟨hb.1, hfront hb.2⟩
  refine ⟨ρ, hρ, hρ0, hρ1, hρrange.trans ?_, hρcost.le⟩
  rintro y ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact hlevel hw

namespace WeightedCollar

theorem frontier_toll_zero
    (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    {B : Set Sphere} {p : Sphere} {g : ℂ → ℝ≥0∞}
    (D : WeightedCollar d.physicalDomain π B p g) (hD : IsOpen D.region)
    (m : Sphere → ℝ≥0∞)
    (hm : ∀z : ℂ, D.function z = D.level → m (π (z : Sphere)) = 0) :
    ∀x ∈ frontier D.region, m x = 0 := by
  intro x hx
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := D.frontier_region_subset hπ hD hx
  exact hm z hz

end WeightedCollar
end CircleDomainRigidity

end

end OAI
