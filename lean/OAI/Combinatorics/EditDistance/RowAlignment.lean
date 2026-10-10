import OAI.Combinatorics.EditDistance.Metric

namespace OAI

/-!
# Charging arbitrary alignments across rows and markers
-/

namespace EditRows
open scoped BigOperators

def payload (B i : ℕ) : Finset ℕ := Finset.Ico (2 * B * i) (2 * B * i + B)
def marker (B i : ℕ) : Finset ℕ := Finset.Ico (2 * B * i + B) (2 * B * i + 2 * B)

lemma mem_payload {B i x : ℕ} : x ∈ payload B i ↔ 2 * B * i ≤ x ∧ x < 2 * B * i + B := by
  simp [payload]

lemma mem_marker {B i x : ℕ} : x ∈ marker B i ↔
    2 * B * i + B ≤ x ∧ x < 2 * B * i + 2 * B := by
  simp [marker]

lemma card_payload (B i : ℕ) : (payload B i).card = B := by simp [payload]
lemma card_marker (B i : ℕ) : (marker B i).card = B := by simp [marker]; omega

lemma payload_before {B i j x y : ℕ} (hij : i < j)
    (hx : x ∈ payload B i) (hy : y ∈ payload B j) : x < y := by
  have hx := mem_payload.mp hx
  have hy := mem_payload.mp hy
  have h : 2 * B * (i + 1) ≤ 2 * B * j := Nat.mul_le_mul_left _ hij
  nlinarith

lemma marker_disjoint {B i j : ℕ} (h : i ≠ j) : Disjoint (marker B i) (marker B j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx := mem_marker.mp hx
  have hy := mem_marker.mp hy
  rcases lt_or_gt_of_ne h with h | h
  · have h' : 2 * B * (i + 1) ≤ 2 * B * j := Nat.mul_le_mul_left _ h
    nlinarith
  · have h' : 2 * B * (j + 1) ≤ 2 * B * i := Nat.mul_le_mul_left _ h
    nlinarith

lemma payload_disjoint {B i j : ℕ} (h : i ≠ j) : Disjoint (payload B i) (payload B j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne h with h | h
  · exact (Nat.lt_irrefl x) (payload_before h hx hy)
  · exact (Nat.lt_irrefl x) (payload_before h hy hx)

lemma payload_subset_range {B L i : ℕ} (hi : i < L) :
    payload B i ⊆ Finset.range (2 * B * L) := by
  intro x hx
  have hx := mem_payload.mp hx
  have h : 2 * B * (i + 1) ≤ 2 * B * L := Nat.mul_le_mul_left _ hi
  simp only [Finset.mem_range]
  nlinarith

lemma marker_subset_range {B L i : ℕ} (hi : i < L) :
    marker B i ⊆ Finset.range (2 * B * L) := by
  intro x hx
  have hx := mem_marker.mp hx
  have h : 2 * B * (i + 1) ≤ 2 * B * L := Nat.mul_le_mul_left _ hi
  simp only [Finset.mem_range]
  nlinarith

lemma payload_index {B : ℕ} (hB : 0 < B) {i x : ℕ} (hx : x ∈ payload B i) :
    x / (2 * B) = i := by
  have hx := mem_payload.mp hx
  apply Nat.div_eq_of_lt_le <;> nlinarith

lemma payload_of_mod {B x : ℕ} (hx : x % (2 * B) < B) :
    x ∈ payload B (x / (2 * B)) := by
  rw [mem_payload]
  have h := Nat.mod_add_div x (2 * B)
  constructor <;> omega

lemma marker_between {B i a b : ℕ} (ha : a ∈ payload B i)
    (hb : i < b / (2 * B)) {x : ℕ} (hx : x ∈ marker B i) : a < x ∧ x < b := by
  have ha := mem_payload.mp ha
  have hx := mem_marker.mp hx
  have h : 2 * B * (i + 1) ≤ 2 * B * (b / (2 * B)) := Nat.mul_le_mul_left _ hb
  have hd := Nat.div_mul_le_self b (2 * B)
  constructor <;> nlinarith

lemma marker_not_payload {B i x : ℕ} (hB : 0 < B) (hx : x ∈ marker B i) :
    ¬ x % (2 * B) < B := by
  intro hp
  have h := payload_of_mod hp
  have hm := mem_marker.mp hx
  have hd : x / (2 * B) = i := by
    apply Nat.div_eq_of_lt_le <;> nlinarith
  rw [hd] at h
  have h := mem_payload.mp h
  omega

section Matching
variable {k B L : ℕ} {f g : Fin k → ℕ}
variable (hf : StrictMono f) (hg : StrictMono g)
include hf hg

def rowMatches (f : Fin k → ℕ) (B i : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun a => f a ∈ payload B i)

def Cross (f g : Fin k → ℕ) (B i : ℕ) : Prop :=
  ∃ a b : Fin k, f a ∈ payload B i ∧ f b ∈ payload B i ∧
    g a / (2 * B) < g b / (2 * B)

lemma crossing_marker_unmatched (hB : 0 < B)
    (hclean : ∀ a : Fin k, ∀ i : ℕ, f a ∈ payload B i → g a % (2 * B) < B)
    {i : ℕ} {a b : Fin k} (ha : f a ∈ payload B i) (hb : f b ∈ payload B i)
    (hab : g a / (2 * B) < g b / (2 * B)) :
    Disjoint (marker B (g a / (2 * B))) (Finset.univ.image g) := by
  apply Finset.disjoint_left.mpr
  intro x hx hxm
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hxm
  obtain ⟨hac, hcb⟩ := marker_between (payload_of_mod (hclean a i ha)) hab hx
  have hac' : a < c := hg.lt_iff_lt.mp hac
  have hcb' : c < b := hg.lt_iff_lt.mp hcb
  have hfa := hf hac'
  have hfb := hf hcb'
  have hc : f c ∈ payload B i := by
    have ha := mem_payload.mp ha
    have hb := mem_payload.mp hb
    rw [mem_payload]
    omega
  exact marker_not_payload hB hx (hclean c i hc)

lemma crossing_marker_distinct {i j : ℕ} (hij : i ≠ j) {a b c d : Fin k}
    (ha : f a ∈ payload B i) (hb : f b ∈ payload B i)
    (hc : f c ∈ payload B j) (hd : f d ∈ payload B j)
    (hab : g a / (2 * B) < g b / (2 * B))
    (hcd : g c / (2 * B) < g d / (2 * B)) :
    g a / (2 * B) ≠ g c / (2 * B) := by
  intro heq
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hbc : b < c := hf.lt_iff_lt.mp (payload_before hij hb hc)
    have hbc' := hg hbc
    have hbc'' : g b / (2 * B) ≤ g c / (2 * B) := Nat.div_le_div_right (Nat.le_of_lt hbc')
    omega
  · have hda : d < a := hf.lt_iff_lt.mp (payload_before hji hd ha)
    have hda' := hg hda
    have hda'' : g d / (2 * B) ≤ g a / (2 * B) := Nat.div_le_div_right (Nat.le_of_lt hda')
    omega

end Matching
end EditRows

namespace EditRows
open scoped BigOperators

lemma sum_cards_le {I X : Type*} [Fintype I] [DecidableEq X]
    (S : I → Finset X) (U : Finset X)
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hsub : ∀ i, S i ⊆ U) : ∑ i, (S i).card ≤ U.card := by
  classical
  have hd : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint S :=
    fun i _ j _ hij => hdisj hij
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
  exact hsub i hx

lemma noncross_loss {k B i t : ℕ} {f g : Fin k → ℕ}
    (hclean : ∀ a : Fin k, f a ∈ payload B i → g a % (2 * B) < B)
    (hcross : ¬ Cross f g B i) (ht : t ≤ B)
    (hlocal : ∀ j : ℕ,
      t + ((rowMatches f B i).filter (fun a => g a ∈ payload B j)).card ≤ B) :
    t + (rowMatches f B i).card ≤ B := by
  classical
  by_cases hne : (rowMatches f B i).Nonempty
  · obtain ⟨a, ha⟩ := hne
    have ha' : f a ∈ payload B i := (Finset.mem_filter.mp ha).2
    have heq : (rowMatches f B i).filter (fun b => g b ∈ payload B (g a / (2 * B))) =
        rowMatches f B i := by
      apply Finset.filter_eq_self.mpr
      intro b hb
      have hb' : f b ∈ payload B i := (Finset.mem_filter.mp hb).2
      have hab : g b / (2 * B) = g a / (2 * B) := by
        by_contra hn
        rcases lt_or_gt_of_ne hn with h | h
        · exact hcross ⟨b, a, hb', ha', h⟩
        · exact hcross ⟨a, b, ha', hb', h⟩
      simpa only [hab] using payload_of_mod (hclean b hb')
    simpa only [heq] using hlocal (g a / (2 * B))
  · have hnil : rowMatches f B i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simpa only [hnil, Finset.card_empty, Nat.add_zero] using ht

lemma source_loss_card {k B i : ℕ} {f : Fin k → ℕ} (hf : Function.Injective f) :
    (payload B i \ Finset.univ.image f).card = B - (rowMatches f B i).card := by
  classical
  have himg : (rowMatches f B i).image f = Finset.univ.image f ∩ payload B i := by
    ext x
    simp only [rowMatches, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_inter]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, rfl⟩, ha⟩
    · rintro ⟨⟨a, rfl⟩, ha⟩
      exact ⟨a, ha, rfl⟩
  rw [Finset.card_sdiff, ← himg, card_payload, Finset.card_image_of_injective _ hf]

lemma unmatched_card {k N : ℕ} {f : Fin k → ℕ} (hf : Function.Injective f)
    (hb : ∀ a, f a < N) :
    (Finset.range N \ Finset.univ.image f).card = N - k := by
  have hsub : Finset.univ.image f ⊆ Finset.range N := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hb a)
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_range,
    Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

theorem matching_loss {k B L t : ℕ} {f g : Fin k → ℕ}
    (hf : StrictMono f) (hg : StrictMono g) (hB : 0 < B)
    (hfb : ∀ a, f a < 2 * B * L) (hgb : ∀ a, g a < 2 * B * L)
    (hclean : ∀ a : Fin k, ∀ i : ℕ, f a ∈ payload B i → g a % (2 * B) < B)
    (ht : t ≤ B)
    (hlocal : ∀ i : Fin L, ∀ j : ℕ,
      t + ((rowMatches f B i).filter (fun a => g a ∈ payload B j)).card ≤ B) :
    L * t ≤ 2 * (2 * B * L - k) := by
  classical
  let C : Finset (Fin L) := Finset.univ.filter (fun i => Cross f g B i)
  have hex : ∀ i : C, ∃ a b : Fin k, f a ∈ payload B i.val ∧
      f b ∈ payload B i.val ∧ g a / (2 * B) < g b / (2 * B) := by
    intro i
    exact (Finset.mem_filter.mp i.property).2
  choose a b ha hb hab using hex
  let S (i : Fin L) : Finset ℕ :=
    if i ∈ C then ∅ else payload B i \ Finset.univ.image f
  let T (i : Fin L) : Finset ℕ :=
    if h : i ∈ C then marker B (g (a ⟨i, h⟩) / (2 * B)) else ∅
  have hsdisj : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    dsimp [S]
    split_ifs with hi hj <;> try simp
    exact (payload_disjoint (Fin.val_ne_of_ne hij)).mono Finset.sdiff_subset Finset.sdiff_subset
  have htdisj : Pairwise (fun i j => Disjoint (T i) (T j)) := by
    intro i j hij
    dsimp [T]
    split_ifs with hi hj <;> try simp
    apply marker_disjoint
    exact crossing_marker_distinct hf hg (Fin.val_ne_of_ne hij)
      (ha ⟨i, hi⟩) (hb ⟨i, hi⟩) (ha ⟨j, hj⟩) (hb ⟨j, hj⟩)
      (hab ⟨i, hi⟩) (hab ⟨j, hj⟩)
  have hssub : ∀ i, S i ⊆ Finset.range (2 * B * L) \ Finset.univ.image f := by
    intro i x hx
    dsimp [S] at hx
    split_ifs at hx with hi
    · simp at hx
    · obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨payload_subset_range i.isLt hp, hn⟩
  have htsub : ∀ i, T i ⊆ Finset.range (2 * B * L) \ Finset.univ.image g := by
    intro i x hx
    dsimp [T] at hx
    split_ifs at hx with hi
    · have hd := crossing_marker_unmatched hf hg hB hclean
        (ha ⟨i, hi⟩) (hb ⟨i, hi⟩) (hab ⟨i, hi⟩)
      have hi' : g (a ⟨i, hi⟩) / (2 * B) < L :=
        (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [Nat.mul_comm] using hgb (a ⟨i, hi⟩))
      exact Finset.mem_sdiff.mpr ⟨marker_subset_range hi' hx, Finset.disjoint_left.mp hd hx⟩
    · simp at hx
  have hsc := sum_cards_le S _ hsdisj hssub
  have htc := sum_cards_le T _ htdisj htsub
  rw [unmatched_card hf.injective hfb] at hsc
  rw [unmatched_card hg.injective hgb] at htc
  have heach : ∀ i : Fin L, t ≤ (S i).card + (T i).card := by
    intro i
    dsimp [S, T]
    split_ifs with hi
    · simpa only [Finset.card_empty, card_marker, Nat.zero_add] using ht
    · simp only [Finset.card_empty, Nat.add_zero, source_loss_card hf.injective]
      have hn : ¬ Cross f g B i := by
        simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and] using hi
      have h := noncross_loss (fun a ha => hclean a i ha) hn ht (hlocal i)
      omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum
  omega

end EditRows

namespace EditRows

theorem matching_loss_real {k B L : ℕ} {t : ℝ} {f g : Fin k → ℕ}
    (hf : StrictMono f) (hg : StrictMono g) (hB : 0 < B)
    (hfb : ∀ a, f a < 2 * B * L) (hgb : ∀ a, g a < 2 * B * L)
    (hclean : ∀ a : Fin k, ∀ i : ℕ, f a ∈ payload B i → g a % (2 * B) < B)
    (ht : t ≤ B)
    (hlocal : ∀ i : Fin L, ∀ j : ℕ,
      t + (((rowMatches f B i).filter (fun a => g a ∈ payload B j)).card : ℝ) ≤ B) :
    (L : ℝ) * t ≤ 2 * ((2 * B * L - k : ℕ) : ℝ) := by
  classical
  by_cases ht0 : 0 ≤ t
  · have hceil : ∀ i : Fin L, ∀ j : ℕ,
        ⌈t⌉₊ + ((rowMatches f B i).filter (fun a => g a ∈ payload B j)).card ≤ B := by
      intro i j
      rw [← Nat.ceil_add_natCast ht0]
      exact Nat.ceil_le.mpr (hlocal i j)
    have h := matching_loss hf hg hB hfb hgb hclean (Nat.ceil_le.mpr ht) hceil
    have h' : (L : ℝ) * (⌈t⌉₊ : ℝ) ≤ 2 * ((2 * B * L - k : ℕ) : ℝ) := by
      exact_mod_cast h
    exact (mul_le_mul_of_nonneg_left (Nat.le_ceil t) (Nat.cast_nonneg L)).trans h'
  · exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg L) (le_of_not_ge ht0)).trans
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))

end EditRows

end OAI
