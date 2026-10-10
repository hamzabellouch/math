import OAI.MeasureTheory.Falconer.Recursion.PolicyInteriorInterval
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union

namespace OAI

namespace PlanarFalconer

inductive PolicyDescriptor where
  | parallel (g p : ℕ)
  | projection (p u : ℕ)
  deriving DecidableEq

def descriptorAnchor : PolicyDescriptor → ℕ
  | .parallel _ p => p
  | .projection p _ => p

def descriptorLength : PolicyDescriptor → ℕ
  | .parallel g p => p-g
  | .projection p u => u-p

noncomputable def originDescriptors (A : ℕ → ℝ) (N q b u : ℕ) : Finset PolicyDescriptor :=
  let p := policyDepth A N q b u
  let l := min (p-b) (u-p)
  (Finset.Ico (p-l) p).image (fun g => PolicyDescriptor.parallel g p) ∪
    if b+u < 2*p then {PolicyDescriptor.projection p u} else ∅

def policyOrigins (N q a t : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N+1)).product (Finset.range (N+1))).filter fun z =>
    a ≤ z.1 ∧ z.2 ≤ t ∧ z.1+100*q < z.2

noncomputable def policyDescriptorList (A : ℕ → ℝ) (N q a t : ℕ) : Finset PolicyDescriptor :=
  (policyOrigins N q a t).biUnion (fun z => originDescriptors A N q z.1 z.2)

theorem policyOrigins_mono {N q a a' t t' : ℕ} (ha : a ≤ a') (ht : t' ≤ t) :
    policyOrigins N q a' t' ⊆ policyOrigins N q a t := by
  intro z hz
  obtain ⟨hz,ha',ht',hwide⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hz,ha.trans ha',ht'.trans ht,hwide⟩

theorem policyDescriptorList_mono (A : ℕ → ℝ) {N q a a' t t' : ℕ}
    (ha : a ≤ a') (ht : t' ≤ t) :
    policyDescriptorList A N q a' t' ⊆ policyDescriptorList A N q a t := by
  intro d hd
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  exact Finset.mem_biUnion.mpr ⟨z,policyOrigins_mono ha ht hz,hd⟩

theorem originDescriptor_anchor (A : ℕ → ℝ) {N q b u : ℕ} {d : PolicyDescriptor}
    (hd : d ∈ originDescriptors A N q b u) : descriptorAnchor d = policyDepth A N q b u := by
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hd
    rfl
  · split_ifs at hd with h
    · have he := Finset.mem_singleton.mp hd
      subst d; rfl
    · simp at hd

theorem policyDescriptor_anchor_mem (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {d : PolicyDescriptor} (hd : d ∈ policyDescriptorList A N q a t) :
    descriptorAnchor d ∈ policyRepresentatives A N q := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,_,_,hwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  rw [originDescriptor_anchor A hd]
  exact policyDepth_mem_representatives A (policyBlocks_nonempty hq huN hwide)

theorem originDescriptor_length (A : ℕ → ℝ) {N q b u : ℕ} (hq : 0 < q)
    (huN : u ≤ N) (hwide : b+100*q < u) {d : PolicyDescriptor}
    (hd : d ∈ originDescriptors A N q b u) :
    0 < descriptorLength d ∧ b ≤ descriptorAnchor d-descriptorLength d ∧
      descriptorAnchor d+descriptorLength d ≤ u := by
  have hne := policyBlocks_nonempty hq huN hwide
  have hp := policyDepth_interior A hq hne
  have hl := policy_move_length A hq hne
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hd
    have hg := Finset.mem_Ico.mp hg
    dsimp only [descriptorLength,descriptorAnchor] at *
    omega
  · split_ifs at hd with h
    · have he := Finset.mem_singleton.mp hd
      subst d
      dsimp only [descriptorLength,descriptorAnchor]
      omega
    · simp at hd

theorem policyDescriptor_origin (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {d : PolicyDescriptor} (hd : d ∈ policyDescriptorList A N q a t) :
    ∃ b u : ℕ, a ≤ b ∧ u ≤ t ∧ b+100*q < u ∧
      descriptorAnchor d = policyDepth A N q b u ∧ 0 < descriptorLength d ∧
      b ≤ descriptorAnchor d-descriptorLength d ∧ descriptorAnchor d+descriptorLength d ≤ u := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,hb,hu,hwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  exact ⟨z.1,z.2,hb,hu,hwide,originDescriptor_anchor A hd,
    originDescriptor_length A hq huN hwide hd⟩

theorem originDescriptors_card (A : ℕ → ℝ) {N q b u : ℕ} (hq : 0 < q)
    (huN : u ≤ N) (hwide : b+100*q < u) : (originDescriptors A N q b u).card ≤ N+1 := by
  classical
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq huN hwide)
  unfold originDescriptors
  apply (Finset.card_union_le _ _).trans
  have hfirst : ((Finset.Ico (policyDepth A N q b u-min (policyDepth A N q b u-b)
      (u-policyDepth A N q b u)) (policyDepth A N q b u)).image
      (fun g => PolicyDescriptor.parallel g (policyDepth A N q b u))).card ≤ N := by
    apply Finset.card_image_le.trans
    rw [Nat.card_Ico]
    omega
  split_ifs <;> simp only [Finset.card_singleton,Finset.card_empty] <;> omega

theorem policyDescriptorList_card (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q) :
    (policyDescriptorList A N q a t).card ≤ (N+1)^3 := by
  classical
  calc
    _ ≤ ∑ z ∈ policyOrigins N q a t, (originDescriptors A N q z.1 z.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ policyOrigins N q a t, (N+1) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hz,_,_,hwide⟩ := Finset.mem_filter.mp hz
      have huN := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
      exact originDescriptors_card A hq huN hwide
    _ = (policyOrigins N q a t).card*(N+1) := by simp
    _ ≤ ((N+1)*(N+1))*(N+1) := by
      apply Nat.mul_le_mul_right
      exact (Finset.card_filter_le _ _).trans (by simp)
    _ = (N+1)^3 := by ring

end PlanarFalconer

end OAI
