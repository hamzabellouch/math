import OAI.Analysis.CircleDomains.Selection.RegularPieceReturn
import Mathlib.Topology.Algebra.Order.Archimedean

namespace OAI

/-! The closed return subgroup of a nonstationary compact regular-level
trajectory has a least positive element. This is its fundamental period. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def CompactRegularPieceFlow.returnSubgroup {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) : AddSubgroup ℝ where
  carrier := {t | F.trajectory x t = x.val}
  zero_mem' := F.initial x
  add_mem' := by
    intro s t hs ht
    exact ((F.periodic_of_return x ht) s).trans hs
  neg_mem' := by
    intro t ht
    change F.trajectory x (-t) = x.val
    simpa only [zero_add] using ((F.periodic_of_return x ht).neg 0).trans (F.initial x)

lemma CompactRegularPieceFlow.returnSubgroup_closed {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) :
    IsClosed (F.returnSubgroup x : Set ℝ) :=
  isClosed_eq (F.trajectory_smooth x).continuous continuous_const

lemma CompactRegularPieceFlow.returnSubgroup_not_dense {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) :
    ¬ Dense (F.returnSubgroup x : Set ℝ) := by
  intro hd
  have he : (F.returnSubgroup x : Set ℝ) = univ :=
    (F.returnSubgroup_closed x).closure_eq.symm.trans hd.closure_eq
  have hc : F.trajectory x = fun _ => x.val := by
    funext t
    have ht : t ∈ (F.returnSubgroup x : Set ℝ) := he.symm ▸ mem_univ t
    exact ht
  exact F.regular x 0 (by rw [hc]; simp)

lemma CompactRegularPieceFlow.exists_least_positive_period {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact K) (x : {z // z ∈ K}) :
    ∃ p : ℝ, IsLeast {t | F.trajectory x t = x.val ∧ 0 < t} p := by
  have hb : F.returnSubgroup x ≠ ⊥ := by
    obtain ⟨p,hp,hper⟩ := F.exists_positive_period hf ha hc x
    intro he
    have hm : p ∈ F.returnSubgroup x := by
      change F.trajectory x p = x.val
      simpa only [zero_add] using (hper 0).trans (F.initial x)
    have hz : p = 0 := by simpa only [he, AddSubgroup.mem_bot] using hm
    exact hp.ne' hz
  by_contra hn
  exact F.returnSubgroup_not_dense x
    ((F.returnSubgroup x).dense_of_no_min hb hn)

lemma CompactRegularPieceFlow.injOn_fundamental_interval {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) {p : ℝ}
    (hp : IsLeast {t | F.trajectory x t = x.val ∧ 0 < t} p) :
    InjOn (F.trajectory x) (Ico 0 p) := by
  intro s hs t ht hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hret := F.return_of_collision x hst
    have hle := hp.2 ⟨hret,sub_pos.mpr hlt⟩
    linarith [hs.1, ht.2]
  · have hret := F.return_of_collision x hst.symm
    have hle := hp.2 ⟨hret,sub_pos.mpr hlt⟩
    linarith [ht.1, hs.2]

lemma CompactRegularPieceFlow.range_levelTrajectory_eq_component {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // z ∈ K}) :
    range (F.levelTrajectory x) = connectedComponent x := by
  have hx : x ∈ range (F.levelTrajectory x) := ⟨0,Subtype.ext (F.initial x)⟩
  exact Subset.antisymm
    ((isPreconnected_range (F.continuous_levelTrajectory x)).subset_connectedComponent hx)
    ((F.isClopen_range_levelTrajectory hf ha x).connectedComponent_subset hx)

end CircleDomainRigidity

end

end OAI
