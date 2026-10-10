import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
Maximal separated extensions give covering nets. Positive separation also gives discreteness,
countability in separable spaces, and finiteness on compact sets.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set TopologicalSpace

theorem exists_separated_cover_extension {X : Type*} [MetricSpace X]
    (E A : Set X) (r : ℝ) (hr : 0 < r) (hAE : A ⊆ E)
    (hA : A.Pairwise fun x y => r ≤ dist x y) :
    ∃ N : Set X, A ⊆ N ∧ N ⊆ E ∧
      N.Pairwise (fun x y => r ≤ dist x y) ∧ ∀ x ∈ E, ∃ z ∈ N, dist x z < r := by
  let S : Set (Set X) := {N | N ⊆ E ∧ N.Pairwise fun x y => r ≤ dist x y}
  obtain ⟨N, hAN, hm⟩ := zorn_subset_nonempty S (by
    intro C hCS hC _
    refine ⟨⋃₀ C, ⟨sUnion_subset (fun B hB => (hCS hB).1), ?_⟩,
      fun B hB => subset_sUnion_of_mem hB⟩
    exact hC.pairwise_sUnion.mpr (fun B hB => (hCS hB).2)) A ⟨hAE, hA⟩
  refine ⟨N, hAN, hm.1.1, hm.1.2, ?_⟩
  intro x hx
  by_contra hcover
  have hfar : ∀ z ∈ N, r ≤ dist x z := by
    intro z hz
    by_contra h
    exact hcover ⟨z, hz, lt_of_not_ge h⟩
  have hins : insert x N ∈ S := by
    refine ⟨insert_subset hx hm.1.1, ?_⟩
    let : Std.Symm (fun a b : X => r ≤ dist a b) :=
      ⟨fun a b h => by simpa only [dist_comm] using! h⟩
    apply (pairwise_insert_of_symm (r := fun a b : X => r ≤ dist a b)).mpr
    exact ⟨hm.1.2, fun z hz _ => hfar z hz⟩
  have hxN : x ∈ N := (hm.2 hins (subset_insert x N)) (mem_insert x N)
  have hh := hfar x hxN
  rw [dist_self] at hh
  linarith

theorem separated_set_countable {X : Type*} [MetricSpace X] [SeparableSpace X]
    (N : Set X) (r : ℝ) (hr : 0 < r)
    (hsep : N.Pairwise fun x y => r ≤ dist x y) : N.Countable := by
  have hd : N.PairwiseDisjoint (fun x => ball x (r / 2)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    linarith [hsep hx hy hxy]
  exact hd.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x _ => ⟨x, mem_ball_self (by positivity)⟩)

theorem separated_set_discrete {X : Type*} [MetricSpace X]
    (N : Set X) (r : ℝ) (hr : 0 < r)
    (hsep : N.Pairwise fun x y => r ≤ dist x y) : IsDiscrete N := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  refine ⟨ball x r, isOpen_ball, ?_⟩
  ext y
  constructor
  · rintro ⟨hyball, hyN⟩
    apply mem_singleton_iff.mpr
    by_contra hyx
    exact (not_lt_of_ge (hsep hyN hx hyx)) hyball
  · intro hy
    rw [mem_singleton_iff.mp hy]
    exact ⟨mem_ball_self hr, hx⟩

theorem separated_set_finite_inter_compact {X : Type*} [MetricSpace X]
    (N K : Set X) (r : ℝ) (hr : 0 < r)
    (hsep : N.Pairwise fun x y => r ≤ dist x y) (hK : IsCompact K) :
    (N ∩ K).Finite := by
  have hclosed : IsClosed N := isClosed_of_pairwise_le_dist hr hsep
  have hcompact : IsCompact (N ∩ K) := hK.inter_left hclosed
  exact hcompact.finite (separated_set_discrete (N ∩ K) r hr (hsep.mono inter_subset_left))

end

end RieszRectifiability

end OAI
