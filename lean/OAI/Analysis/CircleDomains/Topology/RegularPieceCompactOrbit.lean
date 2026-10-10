import OAI.Analysis.CircleDomains.Topology.RegularPieceOpenOrbit
import Mathlib.Topology.Connected.Clopen

namespace OAI

/-! Orbits form clopen components of a compact regular level. Their
compactness forces a return for the complete nonstationary flow. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularPieceFlow.mem_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x y : {z // z ∈ K}) :
    y ∈ range (F.levelTrajectory x) ↔ y.val ∈ range (F.trajectory x) := by
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩
  · rintro ⟨t,ht⟩
    exact ⟨t,Subtype.ext ht⟩

lemma CompactRegularPieceFlow.level_orbits_eq_or_disjoint {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x y : {z // z ∈ K}) :
    range (F.levelTrajectory x) = range (F.levelTrajectory y) ∨
      Disjoint (range (F.levelTrajectory x)) (range (F.levelTrajectory y)) := by
  rcases F.orbits_eq_or_disjoint x y with he | hd
  · left
    ext z
    rw [F.mem_range_levelTrajectory,F.mem_range_levelTrajectory,he]
  · right
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    exact Set.disjoint_left.mp hd ((F.mem_range_levelTrajectory x z).mp hzx)
      ((F.mem_range_levelTrajectory y z).mp hzy)

lemma CompactRegularPieceFlow.isClopen_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // z ∈ K}) : IsClopen (range (F.levelTrajectory x)) := by
  refine ⟨isOpen_compl_iff.mp ?_,F.isOpen_range_levelTrajectory hf ha x⟩
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hyself : y ∈ range (F.levelTrajectory y) := ⟨0,Subtype.ext (F.initial y)⟩
  have hdis : Disjoint (range (F.levelTrajectory x)) (range (F.levelTrajectory y)) := by
    rcases F.level_orbits_eq_or_disjoint x y with he | hd
    · exact (hy (he ▸ hyself)).elim
    · exact hd
  exact Filter.mem_of_superset ((F.isOpen_range_levelTrajectory hf ha y).mem_nhds hyself)
    (fun z hz hx => Set.disjoint_left.mp hdis hx hz)

lemma CompactRegularPieceFlow.compact_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact K) (x : {z // z ∈ K}) :
    IsCompact (range (F.levelTrajectory x)) := by
  let : CompactSpace {z // z ∈ K} := isCompact_iff_compactSpace.mp hc
  exact (F.isClopen_range_levelTrajectory hf ha x).isClosed.isCompact

lemma CompactRegularPieceFlow.not_injective_trajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact K) (x : {z // z ∈ K}) :
    ¬ Injective (F.trajectory x) := by
  intro hi
  have hi' : Injective (F.levelTrajectory x) := fun s t h => hi (congrArg Subtype.val h)
  have he := Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (F.continuous_levelTrajectory x) hi' (F.isOpenMap_levelTrajectory hf ha x)
  have hk : IsCompact (univ : Set ℝ) := he.isEmbedding.isCompact_iff.mpr (by
    simpa only [image_univ] using F.compact_range_levelTrajectory hf ha hc x)
  exact noncompact_univ ℝ hk

end CircleDomainRigidity

end

end OAI
