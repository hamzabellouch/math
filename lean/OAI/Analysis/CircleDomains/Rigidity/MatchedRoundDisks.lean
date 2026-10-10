import OAI.Analysis.CircleDomains.Rigidity.CountableMatchedComponents
import OAI.Analysis.CircleDomains.Sobolev.SourceArea

namespace OAI

/-! Actual round disk parameters for the countable exceptional matched
component pairs. Both radius-square sums follow from their geometry. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 def IndexedMatchedPair := {P : Set Sphere × Set Sphere // D.IsMatchedComponentPair P ∧
    ((interior P.1).Nonempty ∨ (interior P.2).Nonempty)}

 theorem indexedMatchedPair_countable (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) : Countable D.IndexedMatchedPair :=
  (D.countable_matched_nonpoint_components hG hf).to_subtype

 structure MatchedRoundDisks where
  sourceCenter : D.IndexedMatchedPair → ℂ
  targetCenter : D.IndexedMatchedPair → ℂ
  sourceRadius : D.IndexedMatchedPair → ℝ
  targetRadius : D.IndexedMatchedPair → ℝ
  source_nonneg : ∀ j, 0 ≤ sourceRadius j
  target_nonneg : ∀ j, 0 ≤ targetRadius j
  source_eq : ∀ j, j.val.1 = ((↑) : ℂ → Sphere) '' closedBall (sourceCenter j) (sourceRadius j)
  target_eq : ∀ j, j.val.2 = ((↑) : ℂ → Sphere) '' closedBall (targetCenter j) (targetRadius j)
  source_disjoint : Pairwise (Disjoint on fun j => closedBall (sourceCenter j) (sourceRadius j))
  target_disjoint : Pairwise (Disjoint on fun j => closedBall (targetCenter j) (targetRadius j))
  source_summable : Summable (fun j => sourceRadius j^2)
  target_summable : Summable (fun j => targetRadius j^2)

 theorem exists_matched_round_disks (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hG' : IsCircleDomain (f '' G))
    (hinf' : OnePoint.infty ∈ f '' G) : Nonempty D.MatchedRoundDisks := by
  let : Countable D.IndexedMatchedPair := D.indexedMatchedPair_countable hG.1 hf
  choose c r hr he using (fun j : D.IndexedMatchedPair =>
    circle_component_euclidean hG hinf j.property.1.1)
  choose c' s hs he' using (fun j : D.IndexedMatchedPair =>
    circle_component_euclidean hG' hinf' j.property.1.2.1)
  have hd : Pairwise (Disjoint on fun j => closedBall (c j) (r j)) := by
    intro i j hij
    have hne : i.val.1 ≠ j.val.1 := fun h => hij (Subtype.ext
      (IsMatchedComponentPair.fst_injective D i.property.1 j.property.1 h))
    have hdis := i.property.1.1.disjoint_of_ne j.property.1.1 hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    apply Set.disjoint_left.mp hdis
    · rw [he i]
      exact mem_image_of_mem _ hz
    · rw [he j]
      exact mem_image_of_mem _ hz'
  have hd' : Pairwise (Disjoint on fun j => closedBall (c' j) (s j)) := by
    intro i j hij
    have hne : i.val.2 ≠ j.val.2 := fun h => hij (Subtype.ext
      (IsMatchedComponentPair.snd_injective D hG.1 hf i.property.1 j.property.1 h))
    have hdis := i.property.1.2.1.disjoint_of_ne j.property.1.2.1 hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    apply Set.disjoint_left.mp hdis
    · rw [he' i]
      exact mem_image_of_mem _ hz
    · rw [he' j]
      exact mem_image_of_mem _ hz'
  obtain ⟨R,hR,hRb⟩ := ((OnePoint.isOpen_iff_of_mem hinf).mp hG.1).2.isBounded.exists_pos_norm_lt
  obtain ⟨R',hR',hRb'⟩ := ((OnePoint.isOpen_iff_of_mem hinf').mp hG'.1).2.isBounded.exists_pos_norm_lt
  have hcontain (j : D.IndexedMatchedPair) : ball (c j) (r j) ⊆ ball 0 R := by
    intro z hz
    rw [mem_ball,dist_zero_right]
    apply hRb
    have hmem : (z : Sphere) ∈ j.val.1 := by rw [he j]; exact mem_image_of_mem _ (ball_subset_closedBall hz)
    rw [j.property.1.1.eq_component_of_mem hmem] at hmem
    change (z : Sphere) ∈ Gᶜ
    exact connectedComponentIn_subset _ _ hmem
  have hcontain' (j : D.IndexedMatchedPair) : ball (c' j) (s j) ⊆ ball 0 R' := by
    intro z hz
    rw [mem_ball,dist_zero_right]
    apply hRb'
    have hmem : (z : Sphere) ∈ j.val.2 := by rw [he' j]; exact mem_image_of_mem _ (ball_subset_closedBall hz)
    rw [j.property.1.2.1.eq_component_of_mem hmem] at hmem
    change (z : Sphere) ∈ (f '' G)ᶜ
    exact connectedComponentIn_subset _ _ hmem
  exact ⟨⟨c,c',r,s,hr,hs,he,he',hd,hd',
    summable_radii_sq c r R hr (fun i j h => (hd h).mono ball_subset_closedBall ball_subset_closedBall) hcontain,
    summable_radii_sq c' s R' hs (fun i j h => (hd' h).mono ball_subset_closedBall ball_subset_closedBall) hcontain'⟩⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
