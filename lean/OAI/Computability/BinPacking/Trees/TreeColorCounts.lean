import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.SplitIfs
import OAI.Computability.BinPacking.Trees.TreeAttachment
import OAI.Computability.BinPacking.Trees.TreePruning

namespace OAI

namespace BinPackingGap

section

open scoped BigOperators

def phaseQuota (j : ℕ) : ℕ := 2 ^ (j - 1)

@[simp] theorem phaseQuota_succ (j : ℕ) : phaseQuota (j + 1) = 2 ^ j := by
  simp [phaseQuota]

theorem phaseQuota_pos (j : ℕ) : 0 < phaseQuota j := by
  exact Nat.pow_pos (by decide)

def shiftedPhaseQuota (h depth : ℕ) : ℕ := phaseQuota (depth - h)

@[simp] theorem shiftedPhaseQuota_add (h j : ℕ) :
    shiftedPhaseQuota h (h + j) = phaseQuota j := by
  simp [shiftedPhaseQuota]

theorem shiftedPhaseQuota_pos (h depth : ℕ) : 0 < shiftedPhaseQuota h depth :=
  phaseQuota_pos (depth - h)

theorem sum_phaseQuota_add_one (i : ℕ) :
    (∑ j ∈ Finset.Icc 1 i, phaseQuota j) + 1 = 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hset : Finset.Icc 1 (i + 1) = insert (i + 1) (Finset.Icc 1 i) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : i + 1 ∉ Finset.Icc 1 i := by simp
      rw [hset, Finset.sum_insert hnot, phaseQuota_succ, pow_succ]
      omega

theorem sum_phaseQuota (i : ℕ) :
    (∑ j ∈ Finset.Icc 1 i, phaseQuota j) = 2 ^ i - 1 := by
  have h := sum_phaseQuota_add_one i
  omega

theorem sum_phaseQuota_lt (i : ℕ) :
    (∑ j ∈ Finset.Icc 1 i, phaseQuota j) < 2 ^ i := by
  have h := sum_phaseQuota_add_one i
  omega

theorem sum_phaseQuota_initial_add_tail {i N : ℕ} (hiN : i ≤ N) :
    (∑ j ∈ Finset.Icc 1 i, phaseQuota j) +
      (∑ j ∈ Finset.Icc (i + 1) N, phaseQuota j) =
      ∑ j ∈ Finset.Icc 1 N, phaseQuota j := by
  have hset : Finset.Icc 1 N = Finset.Icc 1 i ∪ Finset.Icc (i + 1) N := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Icc 1 i) (Finset.Icc (i + 1) N) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [Finset.mem_Icc] at hj hk
    omega
  rw [hset, Finset.sum_union hd]

theorem sum_phaseQuota_tail {i N : ℕ} (hiN : i ≤ N) :
    (∑ j ∈ Finset.Icc (i + 1) N, phaseQuota j) = 2 ^ N - 2 ^ i := by
  have hsplit := sum_phaseQuota_initial_add_tail hiN
  have hi := sum_phaseQuota_add_one i
  have hN := sum_phaseQuota_add_one N
  omega

def continuationCount (i N : ℕ) : ℕ :=
  1 + ∑ j ∈ Finset.Icc (i + 1) N, phaseQuota j

theorem continuationCount_pos (i N : ℕ) : 0 < continuationCount i N := by
  unfold continuationCount
  omega

@[simp] theorem continuationCount_self (N : ℕ) : continuationCount N N = 1 := by
  simp [continuationCount]

theorem continuationCount_eq {i N : ℕ} (hiN : i ≤ N) :
    continuationCount i N = 1 + (2 ^ N - 2 ^ i) := by
  rw [continuationCount, sum_phaseQuota_tail hiN]

section FiniteMarkings

variable {α : Type*}

theorem card_rank_window_eq (A : Finset α) (rank : α → ℕ) (h lo hi : ℕ) :
    (A.filter (fun x => h + lo < rank x ∧ rank x ≤ h + hi)).card =
      ∑ j ∈ Finset.Icc (lo + 1) hi,
        (A.filter (fun x => rank x = h + j)).card := by
  classical
  calc
    (A.filter (fun x => h + lo < rank x ∧ rank x ≤ h + hi)).card =
        (A.filter (fun x => rank x - h ∈ Finset.Icc (lo + 1) hi)).card := by
      apply congrArg Finset.card
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hx, hlo, hhi⟩
        exact ⟨hx, by omega, by omega⟩
      · rintro ⟨hx, hlo, hhi⟩
        exact ⟨hx, by omega, by omega⟩
    _ = ∑ j ∈ Finset.Icc (lo + 1) hi,
        (A.filter (fun x => rank x - h = j)).card :=
      (Finset.sum_card_fiberwise_eq_card_filter A
        (Finset.Icc (lo + 1) hi) (fun x => rank x - h)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjpos : 1 ≤ j := by
        have := (Finset.mem_Icc.mp hj).1
        omega
      apply congrArg Finset.card
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, hxrank⟩
        exact ⟨hx, by omega⟩
      · rintro ⟨hx, hxrank⟩
        exact ⟨hx, by omega⟩

theorem card_rank_window_le (A : Finset α) (rank : α → ℕ) (q : ℕ → ℕ)
    (h lo hi : ℕ)
    (hquota : ∀ j ∈ Finset.Icc (lo + 1) hi,
      (A.filter (fun x => rank x = h + j)).card ≤ q j) :
    (A.filter (fun x => h + lo < rank x ∧ rank x ≤ h + hi)).card ≤
      ∑ j ∈ Finset.Icc (lo + 1) hi, q j := by
  rw [card_rank_window_eq]
  exact Finset.sum_le_sum hquota

theorem card_rank_interval_le (A : Finset α) (rank : α → ℕ) (p : ℕ → ℕ)
    (h i : ℕ)
    (hquota : ∀ j ∈ Finset.Icc 1 i,
      (A.filter (fun x => rank x = h + j)).card ≤ p (h + j)) :
    (A.filter (fun x => h < rank x ∧ rank x ≤ h + i)).card ≤
      ∑ j ∈ Finset.Icc 1 i, p (h + j) := by
  simpa only [Nat.add_zero, Nat.zero_add] using
    card_rank_window_le A rank (fun j => p (h + j)) h 0 i hquota

theorem card_rank_initial_lt_pow (A : Finset α) (rank : α → ℕ) (h i : ℕ)
    (hquota : ∀ j ∈ Finset.Icc 1 i,
      (A.filter (fun x => rank x = h + j)).card ≤ phaseQuota j) :
    (A.filter (fun x => h < rank x ∧ rank x ≤ h + i)).card < 2 ^ i := by
  have hle := card_rank_window_le A rank phaseQuota h 0 i hquota
  simp only [Nat.add_zero, Nat.zero_add] at hle
  exact lt_of_le_of_lt hle (sum_phaseQuota_lt i)

theorem card_rank_tail_lt_continuations (A : Finset α) (rank : α → ℕ)
    (h i N : ℕ)
    (hquota : ∀ j ∈ Finset.Icc (i + 1) N,
      (A.filter (fun x => rank x = h + j)).card ≤ phaseQuota j) :
    (A.filter (fun x => h + i < rank x ∧ rank x ≤ h + N)).card <
      continuationCount i N := by
  have hle := card_rank_window_le A rank phaseQuota h i N hquota
  unfold continuationCount
  omega

end FiniteMarkings

theorem card_length_interval_le {β : Type*} (A : Finset (List β)) (p : ℕ → ℕ)
    (h i : ℕ)
    (hquota : ∀ j ∈ Finset.Icc 1 i,
      (A.filter (fun w => w.length = h + j)).card ≤ p (h + j)) :
    (A.filter (fun w => h < w.length ∧ w.length ≤ h + i)).card ≤
      ∑ j ∈ Finset.Icc 1 i, p (h + j) :=
  card_rank_interval_le A List.length p h i hquota

end

section
namespace ForkGadget

open scoped BigOperators

def spine (i a : ℕ) : List ℕ := (a + 1) :: List.replicate (i - 1) 1

def continuation (N i b : ℕ) : List ℕ :=
  if i < N then (b + 1) :: List.replicate (N - i - 1) 1 else []

def leafWord (N i a b : ℕ) : List ℕ := spine i a ++ continuation N i b

def leaves (N i : ℕ) : Finset (List ℕ) :=
  ((Finset.range (2 ^ i)).product (Finset.range (continuationCount i N))).image
    (fun ab => leafWord N i ab.1 ab.2)

@[simp] theorem spine_length {i : ℕ} (hi : 1 ≤ i) (a : ℕ) :
    (spine i a).length = i := by
  simp only [spine, List.length_cons, List.length_replicate]
  omega

@[simp] theorem continuation_length {N i : ℕ} (hiN : i ≤ N) (b : ℕ) :
    (continuation N i b).length = N - i := by
  unfold continuation
  split_ifs with h
  · simp only [List.length_cons, List.length_replicate]
    omega
  · simp only [List.length_nil]
    omega

@[simp] theorem leafWord_length {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N)
    (a b : ℕ) : (leafWord N i a b).length = N := by
  simp only [leafWord, List.length_append, spine_length hi, continuation_length hiN]
  omega

theorem spine_injective (i : ℕ) : Function.Injective (spine i) := by
  intro a b h
  have heq : a + 1 = b + 1 := (List.cons.inj h).1
  omega

theorem leafWord_positive (N i a b : ℕ) :
    ∀ x ∈ leafWord N i a b, 0 < x := by
  intro x hx
  simp only [leafWord, List.mem_append] at hx
  rcases hx with hx | hx
  · simp only [spine, List.mem_cons, List.mem_replicate] at hx
    rcases hx with rfl | ⟨_, rfl⟩ <;> omega
  · unfold continuation at hx
    split_ifs at hx with h
    · simp only [List.mem_cons, List.mem_replicate] at hx
      rcases hx with rfl | ⟨_, rfl⟩ <;> omega
    · simp only [List.not_mem_nil] at hx

theorem leafWord_mem {N i a b : ℕ} (ha : a < 2 ^ i)
    (hb : b < continuationCount i N) : leafWord N i a b ∈ leaves N i := by
  exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr hb⟩, rfl⟩

theorem mem_leaves_iff {N i : ℕ} {l : List ℕ} :
    l ∈ leaves N i ↔ ∃ a < 2 ^ i, ∃ b < continuationCount i N,
      leafWord N i a b = l := by
  constructor
  · intro hl
    obtain ⟨ab, hab, heq⟩ := Finset.mem_image.mp hl
    have hab' := Finset.mem_product.mp hab
    exact ⟨ab.1, Finset.mem_range.mp hab'.1, ab.2,
      Finset.mem_range.mp hab'.2, heq⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact leafWord_mem ha hb

def tree (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) : UniformTree where
  height := N
  leaves := leaves N i
  leaves_nonempty := ⟨leafWord N i 0 0,
    leafWord_mem (Nat.two_pow_pos i) (continuationCount_pos i N)⟩
  length_leaf := by
    intro l hl
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_leaves_iff.mp hl
    exact leafWord_length hi hiN a b
  positive_labels := by
    intro l hl
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_leaves_iff.mp hl
    exact leafWord_positive N i a b

@[simp] theorem tree_height (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    (tree N i hi hiN).height = N := rfl

def red (i : ℕ) : Finset (List ℕ) :=
  (Finset.range (phaseQuota i)).image (spine i)

def blue (i : ℕ) : Finset (List ℕ) :=
  (Finset.Ico (phaseQuota i) (2 ^ i)).image (spine i)

theorem two_mul_phaseQuota {i : ℕ} (hi : 1 ≤ i) : 2 * phaseQuota i = 2 ^ i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simp [phaseQuota, pow_succ, Nat.mul_comm]

theorem card_red (i : ℕ) : (red i).card = phaseQuota i := by
  rw [red, Finset.card_image_of_injective _ (spine_injective i), Finset.card_range]

theorem card_blue {i : ℕ} (hi : 1 ≤ i) : (blue i).card = phaseQuota i := by
  rw [blue, Finset.card_image_of_injective _ (spine_injective i), Nat.card_Ico]
  have h := two_mul_phaseQuota hi
  omega

theorem red_depth {i : ℕ} (hi : 1 ≤ i) {w : List ℕ} (hw : w ∈ red i) :
    w.length = i := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
  exact spine_length hi a

theorem blue_depth {i : ℕ} (hi : 1 ≤ i) {w : List ℕ} (hw : w ∈ blue i) :
    w.length = i := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
  exact spine_length hi a

theorem root_not_red {i : ℕ} (hi : 1 ≤ i) : [] ∉ red i := by
  intro h
  have := red_depth hi h
  simp only [List.length_nil] at this
  omega

theorem root_not_blue {i : ℕ} (hi : 1 ≤ i) : [] ∉ blue i := by
  intro h
  have := blue_depth hi h
  simp only [List.length_nil] at this
  omega

theorem red_blue_disjoint (i : ℕ) : Disjoint (red i) (blue i) := by
  apply Finset.disjoint_left.mpr
  intro w hr hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hb
  have hab := spine_injective i heq
  have hlt := Finset.mem_range.mp ha
  have hle := (Finset.mem_Ico.mp hb).1
  omega

theorem spine_mem_vertices {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N)
    {a : ℕ} (ha : a < 2 ^ i) : spine i a ∈ (tree N i hi hiN).vertices := by
  apply (tree N i hi hiN).mem_vertices_iff.mpr
  exact ⟨leafWord N i a 0, leafWord_mem ha (continuationCount_pos i N),
    List.prefix_append _ _⟩

theorem red_subset {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N) :
    red i ⊆ (tree N i hi hiN).vertices := by
  intro w hw
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
  apply spine_mem_vertices hi hiN
  have hlt := Finset.mem_range.mp ha
  have hp := phaseQuota_pos i
  have heq := two_mul_phaseQuota hi
  omega

theorem blue_subset {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N) :
    blue i ⊆ (tree N i hi hiN).vertices := by
  intro w hw
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
  exact spine_mem_vertices hi hiN (Finset.mem_Ico.mp ha).2

private theorem level_le_of_single_depth (marks : Finset (List ℕ)) (i : ℕ)
    (hdepth : ∀ w ∈ marks, w.length = i) (hcard : marks.card = phaseQuota i)
    (depth : ℕ) : levelCount marks depth ≤ phaseQuota depth := by
  by_cases h : depth = i
  · subst depth
    exact (Finset.card_filter_le marks _).trans_eq hcard
  · have hf : marks.filter (fun w => w.length = depth) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw hd
      exact h (hd.symm.trans (hdepth w hw))
    simp only [levelCount, hf, Finset.card_empty, Nat.zero_le]

theorem red_level {i : ℕ} (hi : 1 ≤ i) (depth : ℕ) :
    levelCount (red i) depth ≤ phaseQuota depth :=
  level_le_of_single_depth (red i) i (fun _ hw => red_depth hi hw) (card_red i) depth

theorem blue_level {i : ℕ} (hi : 1 ≤ i) (depth : ℕ) :
    levelCount (blue i) depth ≤ phaseQuota depth :=
  level_le_of_single_depth (blue i) i (fun _ hw => blue_depth hi hw) (card_blue hi) depth

theorem spine_prefix_leafWord_iff {N i a b c : ℕ} (hi : 1 ≤ i) :
    (spine i c).IsPrefix (leafWord N i a b) ↔ c = a := by
  constructor
  · intro h
    have hs : (spine i a).IsPrefix (leafWord N i a b) := List.prefix_append _ _
    rcases List.prefix_or_prefix_of_prefix h hs with hca | hac
    · exact spine_injective i (hca.eq_of_length (by rw [spine_length hi, spine_length hi]))
    · exact (spine_injective i (hac.eq_of_length
        (by rw [spine_length hi, spine_length hi]))).symm
  · rintro rfl
    exact List.prefix_append _ _

private theorem colorCount_spines (I : Finset ℕ) {N i : ℕ} (hi : 1 ≤ i)
    (a b : ℕ) : colorCount (I.image (spine i)) (leafWord N i a b) =
      if a ∈ I then 1 else 0 := by
  have hf : (I.image (spine i)).filter (fun w => w.IsPrefix (leafWord N i a b)) =
      if a ∈ I then {spine i a} else ∅ := by
    ext w
    by_cases ha : a ∈ I
    · simp only [ha, ite_true, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hw, hp⟩
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
        rw [(spine_prefix_leafWord_iff hi).mp hp]
      · rintro rfl
        exact ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, List.prefix_append _ _⟩
    · simp only [ha, ite_false, Finset.mem_filter]
      constructor
      · rintro ⟨hw, hp⟩
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
        exact (ha ((spine_prefix_leafWord_iff hi).mp hp ▸ hc)).elim
      · simp
  unfold colorCount
  rw [hf]
  split_ifs <;> simp

theorem red_count {N i : ℕ} (hi : 1 ≤ i) (a b : ℕ) :
    colorCount (red i) (leafWord N i a b) = if a < phaseQuota i then 1 else 0 := by
  simpa only [red, Finset.mem_range] using
    colorCount_spines (Finset.range (phaseQuota i)) (N := N) hi a b

theorem blue_count {N i : ℕ} (hi : 1 ≤ i) (a b : ℕ) :
    colorCount (blue i) (leafWord N i a b) =
      if phaseQuota i ≤ a ∧ a < 2 ^ i then 1 else 0 := by
  simpa only [blue, Finset.mem_Ico] using
    colorCount_spines (Finset.Ico (phaseQuota i) (2 ^ i)) (N := N) hi a b

theorem total_count {N i : ℕ} (hi : 1 ≤ i) {l : List ℕ} (hl : l ∈ leaves N i) :
    colorCount (red i) l + colorCount (blue i) l = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_leaves_iff.mp hl
  rw [red_count hi, blue_count hi]
  split_ifs <;> omega

theorem red_witness {N i : ℕ} (hi : 1 ≤ i) :
    ∃ l ∈ leaves N i, colorCount (red i) l = 1 := by
  refine ⟨leafWord N i 0 0,
    leafWord_mem (Nat.two_pow_pos i) (continuationCount_pos i N), ?_⟩
  rw [red_count hi, ite_eq_left (phaseQuota_pos i)]

theorem blue_witness {N i : ℕ} (hi : 1 ≤ i) :
    ∃ l ∈ leaves N i, colorCount (blue i) l = 1 := by
  have hlt : phaseQuota i < 2 ^ i := by
    have hp := phaseQuota_pos i
    have heq := two_mul_phaseQuota hi
    omega
  refine ⟨leafWord N i (phaseQuota i) 0,
    leafWord_mem hlt (continuationCount_pos i N), ?_⟩
  rw [blue_count hi, ite_eq_left ⟨le_rfl, hlt⟩]

theorem avoids {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N)
    (A : Finset (List ℕ)) (hroot : [] ∉ A)
    (hquota : ∀ j, 1 ≤ j → j ≤ N → levelCount A j ≤ phaseQuota j) :
    ∃ l ∈ leaves N i, Disjoint A (UniformTree.prefixes l) := by
  let early := A.filter (fun w => 0 < w.length ∧ w.length ≤ i)
  have hearly : early.card < (Finset.range (2 ^ i)).card := by
    simpa only [early, Nat.zero_add, Finset.card_range] using
      card_rank_initial_lt_pow A List.length 0 i (by
        intro j hj
        have hj' := Finset.mem_Icc.mp hj
        simpa only [levelCount, Nat.zero_add] using hquota j hj'.1 (hj'.2.trans hiN))
  have hspines : (Finset.range (2 ^ i) : Set ℕ).PairwiseDisjoint
      (fun a => (UniformTree.prefixes (spine i a)).erase []) := by
    intro a ha b hb hab
    exact disjoint_positive_spine_prefixes hab
  obtain ⟨a, ha, hclear⟩ := exists_disjoint_of_card_lt
    (Finset.range (2 ^ i)) early
    (fun a => (UniformTree.prefixes (spine i a)).erase []) hspines hearly
  have ha' : a < 2 ^ i := Finset.mem_range.mp ha
  have hspine : Disjoint A (UniformTree.prefixes (spine i a)) := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwpath
    by_cases hw : w = []
    · exact hroot (hw ▸ hwA)
    · have hp := UniformTree.mem_prefixes_iff.mp hwpath
      have hlen : w.length ≤ i := by simpa only [spine_length hi] using hp.length_le
      have he : w ∈ early := Finset.mem_filter.mpr
        ⟨hwA, List.length_pos_iff_ne_nil.mpr hw, hlen⟩
      exact Finset.disjoint_left.mp hclear he (Finset.mem_erase.mpr ⟨hw, hwpath⟩)
  by_cases hiN' : i < N
  · let late := A.filter (fun w => i < w.length ∧ w.length ≤ N)
    have hlate : late.card < (Finset.range (continuationCount i N)).card := by
      simpa only [late, Nat.zero_add, Finset.card_range] using
        card_rank_tail_lt_continuations A List.length 0 i N (by
          intro j hj
          have hj' := Finset.mem_Icc.mp hj
          simpa only [levelCount, Nat.zero_add] using hquota j (by omega) hj'.2)
    have hchains : (Finset.range (continuationCount i N) : Set ℕ).PairwiseDisjoint
        (fun b => prefixesAfter (spine i a) (continuation N i b)) := by
      intro b hb c hc hbc
      simp only [continuation, ite_eq_left hiN']
      exact disjoint_spine_prefixesAfter (spine i a) hbc
    obtain ⟨b, hb, hclear'⟩ := exists_disjoint_of_card_lt
      (Finset.range (continuationCount i N)) late
      (fun b => prefixesAfter (spine i a) (continuation N i b)) hchains hlate
    have hchain : Disjoint A (prefixesAfter (spine i a) (continuation N i b)) := by
      apply Finset.disjoint_left.mpr
      intro w hwA hwpath
      obtain ⟨v, hv, hp, hvw⟩ := mem_prefixesAfter_iff.mp hwpath
      have hvpos : 0 < v.length := List.length_pos_iff_ne_nil.mpr hv
      have hvlen : v.length ≤ N - i := by
        simpa only [continuation_length hiN] using hp.length_le
      have hwlen : w.length = i + v.length := by
        rw [← hvw, List.length_append, spine_length hi]
      have hl : w ∈ late := Finset.mem_filter.mpr ⟨hwA, by omega, by omega⟩
      exact Finset.disjoint_left.mp hclear' hl hwpath
    refine ⟨leafWord N i a b, leafWord_mem ha' (Finset.mem_range.mp hb), ?_⟩
    rw [leafWord, prefixes_append_eq]
    apply Finset.disjoint_left.mpr
    intro w hwA hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.disjoint_left.mp hspine hwA hw
    · exact Finset.disjoint_left.mp hchain hwA hw
  · refine ⟨leafWord N i a 0,
      leafWord_mem ha' (continuationCount_pos i N), ?_⟩
    simpa only [leafWord, continuation, ite_eq_right hiN', List.append_nil] using hspine

def auxiliary (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) : AuxiliaryTree 1 where
  tree := tree N i hi hiN
  quota := phaseQuota
  quota_pos := fun depth _ _ => phaseQuota_pos depth
  red := red i
  blue := blue i
  red_subset := red_subset hi hiN
  blue_subset := blue_subset hi hiN
  root_not_red := root_not_red hi
  root_not_blue := root_not_blue hi
  red_blue_disjoint := red_blue_disjoint i
  red_level := fun depth _ _ => red_level hi depth
  blue_level := fun depth _ _ => blue_level hi depth
  total_count := fun _ hl => total_count hi hl
  red_witness := red_witness hi
  blue_witness := blue_witness hi
  avoids := by
    intro A hA
    exact avoids hi hiN A hA.1 hA.2

@[simp] theorem auxiliary_height (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    (auxiliary N i hi hiN).tree.height = N := rfl

@[simp] theorem auxiliary_quota (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    (auxiliary N i hi hiN).quota = phaseQuota := rfl

theorem auxiliary_red_depth (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N)
    {w : List ℕ} (hw : w ∈ (auxiliary N i hi hiN).red) : w.length = i :=
  red_depth hi hw

theorem auxiliary_blue_depth (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N)
    {w : List ℕ} (hw : w ∈ (auxiliary N i hi hiN).blue) : w.length = i :=
  blue_depth hi hw

@[simp] theorem auxiliary_card_red (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    (auxiliary N i hi hiN).red.card = phaseQuota i := card_red i

@[simp] theorem auxiliary_card_blue (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    (auxiliary N i hi hiN).blue.card = phaseQuota i := card_blue hi

end ForkGadget

open scoped BigOperators

namespace UniformTree

theorem marking_card_le (T : UniformTree) (A : Finset T.Node) (q : ℕ → ℕ)
    (hroot : T.root ∉ A)
    (hquota : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      (A.filter (fun v => depth v = ℓ)).card ≤ q ℓ) :
    A.card ≤ ∑ ℓ ∈ Finset.Icc 1 T.height, q ℓ := by
  have hpositive (v : T.Node) (hv : v ∈ A) : 0 < depth v := by
    apply Nat.pos_of_ne_zero
    intro hz
    have heq : v = T.root := (eq_root_iff_depth_eq_zero v).mpr hz
    exact hroot (heq ▸ hv)
  have hfilter : A.filter (fun v => 0 < depth v ∧ depth v ≤ T.height) = A := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact ⟨hpositive v hv, depth_le_height v⟩
  have hsum := card_rank_window_le A depth q 0 0 T.height (by
    intro ℓ hℓ
    have hb := Finset.mem_Icc.mp hℓ
    simpa only [Nat.zero_add] using hquota ℓ hb.1 hb.2)
  simpa only [Nat.zero_add, hfilter] using hsum

end UniformTree

namespace CompetingTrees

theorem markingPlus_card_le {d : ℕ} (T : CompetingTrees d) :
    T.markingPlus.card ≤ T.quotaTotal := by
  have h := T.plus.marking_card_le T.markingPlus T.quota T.plus_root_not_marked (by
    intro ℓ hℓ hL
    exact T.plus_quota ℓ hℓ (by simpa only [T.plus_height] using hL))
  simpa only [T.plus_height, quotaTotal] using h

theorem markingMinus_card_le {d : ℕ} (T : CompetingTrees d) :
    T.markingMinus.card ≤ T.quotaTotal := by
  have h := T.minus.marking_card_le T.markingMinus T.quota T.minus_root_not_marked (by
    intro ℓ hℓ hL
    exact T.minus_quota ℓ hℓ (by simpa only [T.minus_height] using hL))
  simpa only [T.minus_height, quotaTotal] using h

end CompetingTrees
end

namespace UniformTree

def liftMarks (T : UniformTree) (M : T.leaves → Finset (List ℕ)) : Finset (List ℕ) :=
  Finset.univ.biUnion (fun l : T.leaves => (M l).image (fun w => l.val ++ w))

@[simp] theorem mem_liftMarks (T : UniformTree) (M : T.leaves → Finset (List ℕ))
    {x : List ℕ} :
    x ∈ T.liftMarks M ↔ ∃ l : T.leaves, ∃ w ∈ M l, x = l.val ++ w := by
  constructor
  · intro hx
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨w, hw, hx⟩ := Finset.mem_image.mp hl
    exact ⟨l, w, hw, hx.symm⟩
  · rintro ⟨l, w, hw, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨l, Finset.mem_univ l, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩

theorem root_not_mem_lift (T : UniformTree) (M : T.leaves → Finset (List ℕ))
    (hroot : ∀ l, [] ∉ M l) : [] ∉ T.liftMarks M := by
  intro hx
  obtain ⟨l, w, hw, heq⟩ := (T.mem_liftMarks M).mp hx
  have hlen := congrArg List.length heq
  simp only [List.length_nil, List.length_append] at hlen
  have hwzero : w = [] := List.length_eq_zero_iff.mp (by omega)
  exact hroot l (hwzero ▸ hw)

theorem height_lt_length_of_mem_lift (T : UniformTree)
    (M : T.leaves → Finset (List ℕ)) (hroot : ∀ l, [] ∉ M l)
    {x : List ℕ} (hx : x ∈ T.liftMarks M) : T.height < x.length := by
  obtain ⟨l, w, hw, rfl⟩ := (T.mem_liftMarks M).mp hx
  have hwne : w.length ≠ 0 := by
    intro hz
    exact hroot l ((List.length_eq_zero_iff.mp hz) ▸ hw)
  rw [List.length_append, T.length_leaf l.val l.property]
  omega

theorem liftMarks_subset_graft_vertices (T : UniformTree)
    (G : T.leaves → UniformTree) (N : ℕ) (hG : ∀ l, (G l).height = N)
    (M : T.leaves → Finset (List ℕ)) (hM : ∀ l, M l ⊆ (G l).vertices) :
    T.liftMarks M ⊆ (T.graft G N hG).vertices := by
  intro x hx
  obtain ⟨l, w, hw, rfl⟩ := (T.mem_liftMarks M).mp hx
  exact T.append_mem_graft_vertices G N hG l (hM l hw)

theorem old_marks_disjoint_lift (T : UniformTree) (old : Finset (List ℕ))
    (M : T.leaves → Finset (List ℕ)) (hold : old ⊆ T.vertices)
    (hroot : ∀ l, [] ∉ M l) : Disjoint old (T.liftMarks M) := by
  apply Finset.disjoint_left.mpr
  intro x hxold hxlift
  have hle := T.length_le_height (hold hxold)
  have hlt := T.height_lt_length_of_mem_lift M hroot hxlift
  omega

theorem liftMarks_disjoint (T : UniformTree)
    (Mred Mblue : T.leaves → Finset (List ℕ))
    (hdisj : ∀ l, Disjoint (Mred l) (Mblue l)) :
    Disjoint (T.liftMarks Mred) (T.liftMarks Mblue) := by
  apply Finset.disjoint_left.mpr
  intro x hxred hxblue
  obtain ⟨l, u, hu, hequ⟩ := (T.mem_liftMarks Mred).mp hxred
  obtain ⟨m, v, hv, heqv⟩ := (T.mem_liftMarks Mblue).mp hxblue
  obtain ⟨hlm, huv⟩ := (T.append_eq_append_iff l m u v).mp (hequ.symm.trans heqv)
  subst m
  subst v
  exact Finset.disjoint_left.mp (hdisj l) hu hv

theorem union_liftMarks_disjoint (T : UniformTree) (red blue : Finset (List ℕ))
    (Mred Mblue : T.leaves → Finset (List ℕ))
    (hred : red ⊆ T.vertices) (hblue : blue ⊆ T.vertices)
    (hrootred : ∀ l, [] ∉ Mred l) (hrootblue : ∀ l, [] ∉ Mblue l)
    (hold : Disjoint red blue) (hlocal : ∀ l, Disjoint (Mred l) (Mblue l)) :
    Disjoint (red ∪ T.liftMarks Mred) (blue ∪ T.liftMarks Mblue) := by
  apply Finset.disjoint_left.mpr
  intro x hxred hxblue
  rcases Finset.mem_union.mp hxred with hxred | hxred
  · rcases Finset.mem_union.mp hxblue with hxblue | hxblue
    · exact Finset.disjoint_left.mp hold hxred hxblue
    · exact Finset.disjoint_left.mp
        (T.old_marks_disjoint_lift red Mblue hred hrootblue) hxred hxblue
  · rcases Finset.mem_union.mp hxblue with hxblue | hxblue
    · exact Finset.disjoint_left.mp
        (T.old_marks_disjoint_lift blue Mred hblue hrootred) hxblue hxred
    · exact Finset.disjoint_left.mp (T.liftMarks_disjoint Mred Mblue hlocal) hxred hxblue

theorem filter_liftMarks_prefix (T : UniformTree)
    (M : T.leaves → Finset (List ℕ)) (l : T.leaves) (w : List ℕ) :
    (T.liftMarks M).filter (fun x => x.IsPrefix (l.val ++ w)) =
      ((M l).filter (fun v => v.IsPrefix w)).image (fun v => l.val ++ v) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxM, hxp⟩ := Finset.mem_filter.mp hx
    obtain ⟨m, v, hv, rfl⟩ := (T.mem_liftMarks M).mp hxM
    obtain ⟨hml, hvp⟩ := (T.append_prefix_append_iff m l v w).mp hxp
    subst m
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hvp⟩, rfl⟩
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hvM, hvp⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨(T.mem_liftMarks M).mpr ⟨l, v, hvM, rfl⟩,
      (T.append_prefix_append_iff l l v w).mpr ⟨rfl, hvp⟩⟩

theorem colorCount_liftMarks (T : UniformTree)
    (M : T.leaves → Finset (List ℕ)) (l : T.leaves) (w : List ℕ) :
    colorCount (T.liftMarks M) (l.val ++ w) = colorCount (M l) w := by
  unfold colorCount
  rw [T.filter_liftMarks_prefix M l w]
  exact Finset.card_image_of_injective _ (fun _ _ h => List.append_cancel_left h)

theorem colorCount_union_liftMarks (T : UniformTree) (old : Finset (List ℕ))
    (M : T.leaves → Finset (List ℕ)) (hold : old ⊆ T.vertices)
    (hroot : ∀ l, [] ∉ M l) (l : T.leaves) (w : List ℕ) :
    colorCount (old ∪ T.liftMarks M) (l.val ++ w) =
      colorCount old l.val + colorCount (M l) w := by
  have hd : Disjoint (old.filter (fun x => x.IsPrefix (l.val ++ w)))
      ((T.liftMarks M).filter (fun x => x.IsPrefix (l.val ++ w))) :=
    (T.old_marks_disjoint_lift old M hold hroot).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsplit : colorCount (old ∪ T.liftMarks M) (l.val ++ w) =
      colorCount old (l.val ++ w) + colorCount (T.liftMarks M) (l.val ++ w) := by
    unfold colorCount
    rw [Finset.filter_union, Finset.card_union_of_disjoint hd]
  rw [hsplit, T.colorCount_liftMarks M l w]
  have holdcount : colorCount old (l.val ++ w) = colorCount old l.val :=
    congrArg Finset.card (T.filter_old_prefix_append old hold l w)
  rw [holdcount]

theorem levelCount_liftMarks_eq_zero (T : UniformTree)
    (M : T.leaves → Finset (List ℕ)) (hroot : ∀ l, [] ∉ M l)
    {depth : ℕ} (hdepth : depth ≤ T.height) : levelCount (T.liftMarks M) depth = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxM, hxdepth⟩ := Finset.mem_filter.mp hx
  have hlt := T.height_lt_length_of_mem_lift M hroot hxM
  omega

theorem levelCount_liftMarks_le (T : UniformTree)
    (M : T.leaves → Finset (List ℕ)) (rank : T.leaves → ℕ)
    (hinj : Function.Injective rank)
    (hlength : ∀ l, ∀ w ∈ M l, w.length = rank l)
    (hcard : ∀ l, (M l).card ≤ phaseQuota (rank l)) (depth : ℕ) :
    levelCount (T.liftMarks M) depth ≤ phaseQuota (depth - T.height) := by
  classical
  let A := (T.liftMarks M).filter (fun x => x.length = depth)
  by_cases hA : A.Nonempty
  · obtain ⟨x, hx⟩ := hA
    obtain ⟨hxM, hxdepth⟩ := Finset.mem_filter.mp hx
    obtain ⟨l, w, hw, heqx⟩ := (T.mem_liftMarks M).mp hxM
    have hlrank : T.height + rank l = depth := by
      rw [heqx, List.length_append, T.length_leaf l.val l.property, hlength l w hw] at hxdepth
      exact hxdepth
    have hsub : A ⊆ (M l).image (fun v => l.val ++ v) := by
      intro y hy
      obtain ⟨hyM, hydepth⟩ := Finset.mem_filter.mp hy
      obtain ⟨m, v, hv, heqy⟩ := (T.mem_liftMarks M).mp hyM
      have hmrank : T.height + rank m = depth := by
        rw [heqy, List.length_append, T.length_leaf m.val m.property, hlength m v hv] at hydepth
        exact hydepth
      have hml : m = l := hinj (by omega)
      subst m
      exact Finset.mem_image.mpr ⟨v, hv, heqy.symm⟩
    have hrank : rank l = depth - T.height := by omega
    calc
      levelCount (T.liftMarks M) depth = A.card := rfl
      _ ≤ ((M l).image (fun v => l.val ++ v)).card := Finset.card_le_card hsub
      _ ≤ (M l).card := Finset.card_image_le
      _ ≤ phaseQuota (rank l) := hcard l
      _ = phaseQuota (depth - T.height) := congrArg phaseQuota hrank
  · have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ _
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

theorem levelCount_union_liftMarks (T : UniformTree) (old : Finset (List ℕ))
    (M : T.leaves → Finset (List ℕ)) (hold : old ⊆ T.vertices)
    (hroot : ∀ l, [] ∉ M l) (depth : ℕ) :
    levelCount (old ∪ T.liftMarks M) depth =
      if depth ≤ T.height then levelCount old depth else levelCount (T.liftMarks M) depth := by
  unfold levelCount
  split_ifs with hdepth
  · apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hxold | hxlift, hxlen⟩
      · exact ⟨hxold, hxlen⟩
      · have hlt := T.height_lt_length_of_mem_lift M hroot hxlift
        omega
    · rintro ⟨hxold, hxlen⟩
      exact ⟨Or.inl hxold, hxlen⟩
  · apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hxold | hxlift, hxlen⟩
      · have hle := T.length_le_height (hold hxold)
        omega
      · exact ⟨hxlift, hxlen⟩
    · rintro ⟨hxlift, hxlen⟩
      exact ⟨Or.inr hxlift, hxlen⟩

theorem levelCount_union_liftMarks_le (T : UniformTree) (old : Finset (List ℕ))
    (M : T.leaves → Finset (List ℕ))
    (hold : old ⊆ T.vertices) (hroot : ∀ l, [] ∉ M l)
    (rank : T.leaves → ℕ) (hinj : Function.Injective rank)
    (hlength : ∀ l, ∀ w ∈ M l, w.length = rank l)
    (hcard : ∀ l, (M l).card ≤ phaseQuota (rank l)) (quota : ℕ → ℕ)
    (holdquota : ∀ depth, 1 ≤ depth → depth ≤ T.height → levelCount old depth ≤ quota depth)
    (depth : ℕ) (hpos : 1 ≤ depth) :
    levelCount (old ∪ T.liftMarks M) depth ≤
      if depth ≤ T.height then quota depth else phaseQuota (depth - T.height) := by
  rw [T.levelCount_union_liftMarks old M hold hroot depth]
  split_ifs with hdepth
  · exact holdquota depth hpos hdepth
  · exact T.levelCount_liftMarks_le M rank hinj hlength hcard depth

end UniformTree
end BinPackingGap

end OAI
