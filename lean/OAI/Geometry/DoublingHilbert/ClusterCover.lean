import Mathlib
import OAI.Geometry.DoublingHilbert.IntrinsicCovers
import OAI.Geometry.DoublingHilbert.CompactUnion
import OAI.Geometry.DoublingHilbert.ClusterScales

namespace OAI

open Set Metric
open scoped BigOperators
open Filter
open scoped Topology
noncomputable section
namespace CompactBanach

theorem ambient_doubling_clusters
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (C : ℕ → Finset B) {v : B} (hv : ‖v‖ = 1)
    (hloc : ∀ j z, z ∈ C j → dist z (clusterScale j • v) ≤ clusterScale j / 100)
    {L : ℕ} (hC : ∀ j, AmbientDoubling (C j : Set B) L) :
    AmbientDoubling ({0} ∪ ⋃ j : ℕ, (C j : Set B)) (1 + 5 * L ^ 2) := by
  classical
  intro x _ r hr
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (clusterScale_tendsto.eventually (gt_mem_nhds (show (0 : ℝ) < r / 4 by positivity)))
  let I : Finset ℕ := (Finset.range N).filter fun j =>
    r / 4 < clusterScale j ∧ ∃ z ∈ C j, dist z x < r
  have hImem {j : ℕ} (hj : j ∈ I) :
      r / 4 < clusterScale j ∧ ∃ z ∈ C j, dist z x < r :=
    (Finset.mem_filter.mp hj).2
  have hIcard : I.card ≤ 5 := by
    by_cases hsmall : I.card ≤ 1
    · omega
    · have hbig : 1 < I.card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hbig
      have hne : I.Nonempty := ⟨a, ha⟩
      let i := I.min' hne
      have hi : i ∈ I := I.min'_mem hne
      have hex : ∃ j ∈ I, i < j := by
        by_cases hai : a = i
        · refine ⟨b, hb, ?_⟩
          have hle : i ≤ b := I.min'_le b hb
          omega
        · refine ⟨a, ha, ?_⟩
          have hle : i ≤ a := I.min'_le a ha
          omega
      obtain ⟨j, hj, hij⟩ := hex
      obtain ⟨p, hp, hpx⟩ := (hImem hi).2
      obtain ⟨q, hq, hqx⟩ := (hImem hj).2
      have hs := cluster_separation hv hij (hloc i p hp) (hloc j q hq)
      have ht := dist_triangle p x q
      rw [dist_comm x q] at ht
      have hi_bound : clusterScale i ≤ (400 / 97 : ℝ) * r := by linarith
      apply five_scales hr I (fun k hk => (hImem hk).1)
      intro k hk
      exact (clusterScale_antitone (I.min'_le k hk)).trans hi_bound
  have hcover (j : I) : ∃ d : Finset B,
      (∀ z ∈ d, z ∈ C j.val) ∧ d.card ≤ L ^ 2 ∧
        ∀ z ∈ C j.val, dist z x < r → ∃ w ∈ d, dist z w < r / 2 := by
    obtain ⟨y, hy, hyx⟩ := (hImem j.property).2
    obtain ⟨d, hd, hcard, hcov⟩ :=
      ambient_iterated_cover (hC j.val) 2 hy (show 0 < 2 * r by positivity)
    refine ⟨d, hd, hcard, ?_⟩
    intro z hz hzx
    have hzy : dist z y < 2 * r := by
      have h := dist_triangle z x y
      rw [dist_comm x y] at h
      linarith
    obtain ⟨w, hw, hzw⟩ := hcov z hz hzy
    norm_num at hzw
    exact ⟨w, hw, by linarith⟩
  choose d hdK hdcard hdcov using hcover
  let centers : Finset B := insert 0 (I.attach.biUnion d)
  have hzero : (0 : B) ∈ centers := Finset.mem_insert_self _ _
  refine ⟨centers, ?_, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Or.inl (by simp)
    · obtain ⟨j, _, hzj⟩ := Finset.mem_biUnion.mp hz
      exact Or.inr (mem_iUnion.mpr ⟨j.val, hdK j z hzj⟩)
  · calc
      centers.card ≤ (I.attach.biUnion d).card + 1 := Finset.card_insert_le _ _
      _ ≤ (∑ j ∈ I.attach, (d j).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ (∑ _j ∈ I.attach, L ^ 2) + 1 :=
        Nat.add_le_add_right (Finset.sum_le_sum fun j _ => hdcard j) _
      _ = I.card * L ^ 2 + 1 := by simp
      _ ≤ 5 * L ^ 2 + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right _ hIcard) _
      _ = 1 + 5 * L ^ 2 := by omega
  · intro z hz hzx
    rcases hz with hz | hz
    · have hz0 := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨0, hzero, by simpa using half_pos hr⟩
    · obtain ⟨j, hzj⟩ := mem_iUnion.mp hz
      by_cases hj : clusterScale j ≤ r / 4
      · refine ⟨0, hzero, ?_⟩
        rw [dist_zero_right]
        have hn := cluster_norm_bound hv (hloc j z hzj)
        linarith
      · have hjN : j < N := by
          by_contra! hn
          have h := hN j hn
          linarith
        have hjI : j ∈ I := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hjN, lt_of_not_ge hj, z, hzj, hzx⟩
        obtain ⟨w, hw, hzw⟩ := hdcov ⟨j, hjI⟩ z hzj hzx
        exact ⟨w, Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨⟨j, hjI⟩, Finset.mem_attach _ _, hw⟩), hzw⟩

                                                                            
                                                                          
                                                                                
theorem compact_doubling_clusters
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (C : ℕ → Finset B) {v : B} (hv : ‖v‖ = 1)
    (hloc : ∀ j z, z ∈ C j → dist z (clusterScale j • v) ≤ clusterScale j / 100)
    {L : ℕ} (hC : ∀ j, DoublingAtMost (C j : Set B) L) :
    IsCompact ({0} ∪ ⋃ j : ℕ, (C j : Set B)) ∧
      DoublingAtMost ({0} ∪ ⋃ j : ℕ, (C j : Set B)) (1 + 5 * L ^ 2) := by
  refine ⟨compact_shrinking_union 0 C ?_,
    doubling_iff_ambient.mpr (ambient_doubling_clusters C hv hloc
      (fun j => doubling_iff_ambient.mp (hC j)))⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (clusterScale_tendsto.eventually
      (gt_mem_nhds (show (0 : ℝ) < ε * (100 / 101) by positivity)))
  refine ⟨N, fun j hj z hz => ?_⟩
  rw [dist_zero_right]
  have hn := cluster_norm_bound hv (hloc j z hz)
  have ht := hN j hj
  linarith

end CompactBanach
end

end OAI
