import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace OAI

namespace Balanced.CoverObstruction

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α]

theorem card_le_sum_inter_card_of_cover
    (F : Finset α) (s : Finset ι) (block : ι → Finset α)
    (hcover : F ⊆ s.biUnion block) :
    F.card ≤ ∑ i ∈ s, (F ∩ block i).card := by
  have hsub : F ⊆ s.biUnion (fun i => F ∩ block i) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp (hcover hx)
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨hx, hxi⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

theorem card_le_initial_add_sum_inter_card_of_cover
    (F Z : Finset α) (s : Finset ι) (block : ι → Finset α)
    (hcover : F ⊆ Z ∪ s.biUnion block) :
    F.card ≤ (F ∩ Z).card + ∑ i ∈ s, (F ∩ block i).card := by
  have hsub : F ⊆ (F ∩ Z) ∪ s.biUnion (fun i => F ∩ block i) := by
    intro x hx
    rcases Finset.mem_union.mp (hcover hx) with hz | hb
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hz⟩)
    · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hb
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨hx, hxi⟩⟩)
  calc
    F.card ≤ ((F ∩ Z) ∪ s.biUnion (fun i => F ∩ block i)).card :=
      Finset.card_le_card hsub
    _ ≤ (F ∩ Z).card + (s.biUnion (fun i => F ∩ block i)).card :=
      Finset.card_union_le _ _
    _ ≤ (F ∩ Z).card + ∑ i ∈ s, (F ∩ block i).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _

theorem card_le_initial_add_capacity_of_cover
    (F Z : Finset α) (s : Finset ι) (block : ι → Finset α) (capacity : ℕ)
    (hcover : F ⊆ Z ∪ s.biUnion block)
    (hcapacity : ∀ i ∈ s, (F ∩ block i).card ≤ capacity) :
    F.card ≤ Z.card + s.card * capacity := by
  calc
    F.card ≤ (F ∩ Z).card + ∑ i ∈ s, (F ∩ block i).card :=
      card_le_initial_add_sum_inter_card_of_cover F Z s block hcover
    _ ≤ Z.card + ∑ i ∈ s, capacity := by
      exact Nat.add_le_add (Finset.card_le_card Finset.inter_subset_right)
        (Finset.sum_le_sum hcapacity)
    _ = Z.card + s.card * capacity := by simp

variable [DecidableEq ι]

omit [DecidableEq ι] in
theorem card_le_inter_initial_add_capacity_of_cover
    (F Z : Finset α) (s : Finset ι) (block : ι → Finset α) (capacity : ℕ)
    (hcover : F ⊆ Z ∪ s.biUnion block)
    (hcapacity : ∀ i ∈ s, (F ∩ block i).card ≤ capacity) :
    F.card ≤ (F ∩ Z).card + s.card * capacity := by
  calc
    F.card ≤ (F ∩ Z).card + ∑ i ∈ s, (F ∩ block i).card :=
      card_le_initial_add_sum_inter_card_of_cover F Z s block hcover
    _ ≤ (F ∩ Z).card + ∑ i ∈ s, capacity :=
      Nat.add_le_add_left (Finset.sum_le_sum hcapacity) _
    _ = (F ∩ Z).card + s.card * capacity := by simp

theorem cover_split_selected
    (F : Finset α) (C pencil : Finset ι) (block : ι → Finset α)
    (hcover : F ⊆ C.biUnion block) :
    F ⊆ pencil.biUnion block ∪ (C \ pencil).biUnion block := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp (hcover hx)
  by_cases hip : i ∈ pencil
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hip, hxi⟩)
  · exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hip⟩, hxi⟩)

theorem card_le_pencil_capacity_of_cover
    (F : Finset α) (C pencil : Finset ι) (block : ι → Finset α)
    (initial capacity : ℕ) (hcover : F ⊆ C.biUnion block)
    (hpencil : (F ∩ pencil.biUnion block).card ≤ initial)
    (hcapacity : ∀ i ∈ C \ pencil, (F ∩ block i).card ≤ capacity) :
    F.card ≤ initial + (C \ pencil).card * capacity := by
  exact (card_le_inter_initial_add_capacity_of_cover F (pencil.biUnion block)
    (C \ pencil) block capacity (cover_split_selected F C pencil block hcover)
    hcapacity).trans (Nat.add_le_add_right hpencil _)

theorem second_constituent_occupancy_contradiction
    (F : Finset α) (C pencil : Finset ι) (block : ι → Finset α)
    (q ρ : ℝ) (B : ℕ)
    (hsize : 2 * (1 + (B : ℝ)) < ρ * q)
    (hoccupancy : ρ * q ≤ F.card)
    (houtside : ((C \ pencil).card : ℝ) ≤ ρ * q / 4)
    (hpencil : (F ∩ pencil.biUnion block).card ≤ 1 + B)
    (hcapacity : ∀ i ∈ C \ pencil, (F ∩ block i).card ≤ 2) :
    ¬ F ⊆ C.biUnion block := by
  intro hcover
  have h := card_le_pencil_capacity_of_cover F C pencil block (1 + B) 2
    hcover hpencil hcapacity
  have hr : (F.card : ℝ) ≤ 1 + (B : ℝ) + ((C \ pencil).card : ℝ) * 2 := by
    exact_mod_cast h
  linarith

theorem affine_line_occupancy_contradiction
    (F : Finset α) (C pencil : Finset ι) (block : ι → Finset α)
    (q ρ : ℝ) (hsize : 2 < ρ * q)
    (hoccupancy : ρ * q ≤ F.card)
    (houtside : ((C \ pencil).card : ℝ) ≤ ρ * q / 4)
    (hpencil : (F ∩ pencil.biUnion block).card ≤ 1)
    (hcapacity : ∀ i ∈ C \ pencil, (F ∩ block i).card ≤ 1) :
    ¬ F ⊆ C.biUnion block := by
  intro hcover
  have h := card_le_pencil_capacity_of_cover F C pencil block 1 1
    hcover hpencil hcapacity
  have hr : (F.card : ℝ) ≤ 1 + ((C \ pencil).card : ℝ) := by
    exact_mod_cast (by simpa using h : F.card ≤ 1 + (C \ pencil).card)
  linarith

theorem parallel_line_occupancy_contradiction
    (F : Finset α) (C pencil : Finset ι) (block : ι → Finset α)
    (q ρ : ℝ) (hpositive : 0 < ρ * q)
    (hoccupancy : ρ * q ≤ F.card)
    (houtside : ((C \ pencil).card : ℝ) ≤ ρ * q / 4)
    (hpencil : Disjoint F (pencil.biUnion block))
    (hcapacity : ∀ i ∈ C \ pencil, (F ∩ block i).card ≤ 1) :
    ¬ F ⊆ C.biUnion block := by
  intro hcover
  have h := card_le_pencil_capacity_of_cover F C pencil block 0 1 hcover
    (by simp [Finset.disjoint_iff_inter_eq_empty.mp hpencil]) hcapacity
  have hr : (F.card : ℝ) ≤ ((C \ pencil).card : ℝ) := by
    exact_mod_cast (by simpa using h : F.card ≤ (C \ pencil).card)
  linarith

theorem cover_by_remaining_of_forced_disjoint
    (F : Finset α) (C forced : Finset ι) (block : ι → Finset α)
    (hcover : F ⊆ C.biUnion block)
    (hmiss : ∀ i ∈ forced, Disjoint F (block i)) :
    F ⊆ (C \ forced).biUnion block := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp (hcover hx)
  have hnot : i ∉ forced := by
    intro hif
    exact Finset.disjoint_left.mp (hmiss i hif) hx hxi
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hnot⟩, hxi⟩

theorem remaining_card_le_split_count_sub_one
    (C forced : Finset ι) (q b : ℕ)
    (hforced : forced ⊆ C) (hsize : C.card ≤ q)
    (hb : b ≤ q + 1) (hcount : forced.card = q + 1 - b) :
    (C \ forced).card ≤ b - 1 := by
  have hcard := Finset.card_sdiff_add_card_eq_card hforced
  omega

theorem remaining_card_le_three
    (C forced : Finset ι) (q : ℕ)
    (hq : 3 ≤ q) (hforced : forced ⊆ C)
    (hsize : C.card ≤ q) (hcount : forced.card = q - 3) :
    (C \ forced).card ≤ 3 := by
  have hcard := Finset.card_sdiff_add_card_eq_card hforced
  omega

omit [DecidableEq ι] in
theorem eight_points_not_covered_by_three_pairs
    (F : Finset α) (s : Finset ι) (block : ι → Finset α)
    (hF : F.card = 8) (hs : s.card ≤ 3)
    (hcapacity : ∀ i ∈ s, (F ∩ block i).card ≤ 2) :
    ¬ F ⊆ s.biUnion block := by
  intro hcover
  have h := card_le_initial_add_capacity_of_cover F ∅ s block 2
    (by simpa using hcover) hcapacity
  simp only [Finset.card_empty, zero_add] at h
  omega

omit [DecidableEq ι] in
theorem eight_points_not_covered_by_two_and_four
    (F Z : Finset α) (s : Finset ι) (block : ι → Finset α)
    (hF : F.card = 8) (hZ : Z.card ≤ 2) (hs : s.card ≤ 1)
    (hcapacity : ∀ i ∈ s, (F ∩ block i).card ≤ 4) :
    ¬ F ⊆ Z ∪ s.biUnion block := by
  intro hcover
  have h := card_le_initial_add_capacity_of_cover F Z s block 4 hcover hcapacity
  omega

theorem parallel_pencil_cover_impossible
    (F : Finset α) (C forced : Finset ι) (block : ι → Finset α) (q : ℕ)
    (hq : 3 ≤ q) (hF : F.card = 8)
    (hforced : forced ⊆ C) (hsize : C.card ≤ q)
    (hcount : forced.card = q - 3)
    (hmiss : ∀ i ∈ forced, Disjoint F (block i))
    (hcapacity : ∀ i ∈ C \ forced, (F ∩ block i).card ≤ 2) :
    ¬ F ⊆ C.biUnion block := by
  intro hcover
  exact eight_points_not_covered_by_three_pairs F (C \ forced) block hF
    (remaining_card_le_three C forced q hq hforced hsize hcount) hcapacity
    (cover_by_remaining_of_forced_disjoint F C forced block hcover hmiss)

theorem occupancy_numeric_margins
    (q B ρ : ℝ) (hq : 0 < q) (hB : 0 ≤ B) (hρ : ρ < 1)
    (hsize : 2 * (1 + B) < ρ * q) :
    B < q ∧ 1 + ρ * q / 4 < ρ * q ∧
      1 + B + ρ * q / 2 < ρ * q := by
  constructor
  · nlinarith
  constructor <;> linarith

end Balanced.CoverObstruction

end OAI
