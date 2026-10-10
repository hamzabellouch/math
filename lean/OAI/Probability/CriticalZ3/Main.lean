import OAI.Probability.CriticalZ3.Subunit

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical

/-- Vanishing origin order parameter at the exact bond critical infimum. -/
theorem bond_critical_origin : bondLaw bondCritical (bondInfiniteAt 0) = 0 := by
  by_cases hc : bondCritical = 0
  · simp only [hc,bondLaw_zero_infinite]
  · have hp : 0 < bondCritical := lt_of_le_of_ne bondCritical_mem.1 (Ne.symm hc)
    by_contra hn
    have hpos : 0 < bondLaw bondCritical (bondInfiniteAt 0) := bot_lt_iff_ne_bot.mpr hn
    obtain ⟨q,hq,hqc,hqpos⟩ := Coarse.lower_percolating_parameter .bond hp bondCritical_lt_one hpos
    exact (ne_of_gt hqpos) (bond_subcritical_origin hq hqc)

/-- Vanishing origin order parameter at the separate site critical infimum. -/
theorem site_critical_origin : siteLaw siteCritical (siteInfiniteAt 0) = 0 := by
  by_cases hc : siteCritical = 0
  · simp only [hc,siteLaw_zero_infinite]
  · have hp : 0 < siteCritical := lt_of_le_of_ne siteCritical_mem.1 (Ne.symm hc)
    by_contra hn
    have hpos : 0 < siteLaw siteCritical (siteInfiniteAt 0) := bot_lt_iff_ne_bot.mpr hn
    obtain ⟨q,hq,hqc,hqpos⟩ := Coarse.lower_percolating_parameter .site hp siteCritical_lt_one hpos
    exact (ne_of_gt hqpos) (site_subcritical_origin hq hqc)

namespace SignedSymmetry

theorem bondConnected_map (S : SignedSymmetry) (ω : BondConfig) (x y : Vertex) :
    BondConnected (fun e => ω (S.bond e)) x y ↔ BondConnected ω (S.vertex x) (S.vertex y) :=
  rtg_equiv_iff S.vertex (S.bondOpen_map ω) x y

theorem siteConnected_map (S : SignedSymmetry) (ω : SiteConfig) (x y : Vertex) :
    SiteConnected (fun e => ω (S.vertex e)) x y ↔ SiteConnected ω (S.vertex x) (S.vertex y) :=
  and_congr_right (fun _ => rtg_equiv_iff S.vertex (S.siteOpen_map ω) x y)

theorem bondInfiniteAt_map (S : SignedSymmetry) (ω : BondConfig) (x : Vertex) :
    (fun e => ω (S.bond e)) ∈ bondInfiniteAt x ↔ ω ∈ bondInfiniteAt (S.vertex x) := by
  have he : bondCluster (fun e => ω (S.bond e)) x = S.vertex ⁻¹' bondCluster ω (S.vertex x) := by
    ext y
    exact S.bondConnected_map ω x y
  change (bondCluster (fun e => ω (S.bond e)) x).Infinite ↔ _
  rw [he]
  constructor
  · intro hi hf
    exact hi (Set.Finite.preimage S.vertex.injective.injOn hf)
  · intro hi
    exact hi.preimage (fun y _ => S.vertex.surjective y)

theorem siteInfiniteAt_map (S : SignedSymmetry) (ω : SiteConfig) (x : Vertex) :
    (fun e => ω (S.vertex e)) ∈ siteInfiniteAt x ↔ ω ∈ siteInfiniteAt (S.vertex x) := by
  have he : siteCluster (fun e => ω (S.vertex e)) x = S.vertex ⁻¹' siteCluster ω (S.vertex x) := by
    ext y
    exact S.siteConnected_map ω x y
  change (siteCluster (fun e => ω (S.vertex e)) x).Infinite ↔ _
  rw [he]
  constructor
  · intro hi hf
    exact hi (Set.Finite.preimage S.vertex.injective.injOn hf)
  · intro hi
    exact hi.preimage (fun y _ => S.vertex.surjective y)
end SignedSymmetry

theorem bondInfiniteAt_probability (p : ℝ) (x : Vertex) :
    bondLaw p (bondInfiniteAt x) = bondLaw p (bondInfiniteAt 0) := by
  let S := faceSymmetry x canonicalFace
  have he : (fun ω e => ω (S.bond e)) ⁻¹' bondInfiniteAt 0 = bondInfiniteAt x := by
    ext ω
    simp only [Set.mem_preimage,S.bondInfiniteAt_map,faceSymmetry_zero,S]
  have h := ProductCylinder.reindex_probability S.bond (parameter p) (bondInfiniteAt 0)
    (measurableSet_bondInfiniteAt 0)
  rw [he] at h
  exact h

theorem siteInfiniteAt_probability (p : ℝ) (x : Vertex) :
    siteLaw p (siteInfiniteAt x) = siteLaw p (siteInfiniteAt 0) := by
  let S := faceSymmetry x canonicalFace
  have he : (fun ω e => ω (S.vertex e)) ⁻¹' siteInfiniteAt 0 = siteInfiniteAt x := by
    ext ω
    simp only [Set.mem_preimage,S.siteInfiniteAt_map,faceSymmetry_zero,S]
  have h := ProductCylinder.reindex_probability S.vertex (parameter p) (siteInfiniteAt 0)
    (measurableSet_siteInfiniteAt 0)
  rw [he] at h
  exact h

/-- Nearest-neighbor bond percolation on Z³ has almost surely no infinite cluster at criticality. -/
theorem bond_critical_no_infinite :
    ∀ᵐ ω ∂bondLaw bondCritical, ∀ x : Vertex, (bondCluster ω x).Finite := by
  rw [ae_all_iff]
  intro x
  rw [ae_iff]
  exact (bondInfiniteAt_probability bondCritical x).trans bond_critical_origin

/-- Nearest-neighbor site percolation on Z³ has almost surely no infinite cluster at its own criticality. -/
theorem site_critical_no_infinite :
    ∀ᵐ ω ∂siteLaw siteCritical, ∀ x : Vertex, (siteCluster ω x).Finite := by
  rw [ae_all_iff]
  intro x
  rw [ae_iff]
  exact (siteInfiniteAt_probability siteCritical x).trans site_critical_origin

theorem critical_no_infinite :
    (∀ᵐ ω ∂bondLaw bondCritical, ∀ x : Vertex, (bondCluster ω x).Finite) ∧
    (∀ᵐ ω ∂siteLaw siteCritical, ∀ x : Vertex, (siteCluster ω x).Finite) :=
  ⟨bond_critical_no_infinite, site_critical_no_infinite⟩

end CriticalZ3

end OAI
