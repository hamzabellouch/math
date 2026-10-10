import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationMasks
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ResidueFilters
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Entropy
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ResidueMatchAccounting

namespace OAI

/-!
# Raw representation universes before prefixes or the extra prime

A raw leaf occurrence records its three actual subset choices. Products of
these occurrences retain repeated weights and locally overlapping masks.
Only the valid-entry universe removes overlapping local masks and deduplicates
by exact weight and top mask. These are the universes counted by `G`, `J`, `U`.
-/

noncomputable section

namespace LowSpaceSubsetSum

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure RepresentationLeaf (ι : Type*) where
  top : Finset ι
  mixer : Finset ι
  background : Finset ι
  topCount : ℕ
  localCount : ℕ

namespace RepresentationLeaf

abbrev Occurrence (ι : Type*) := (Finset ι × Finset ι) × Finset ι

def occurrences (L : RepresentationLeaf ι) : Finset (Occurrence ι) :=
  (L.top.powersetCard L.topCount ×ˢ L.mixer.powersetCard L.localCount) ×ˢ L.background.powerset

def occurrenceWeight (a : ι → ℤ) (x : Occurrence ι) : ℤ :=
  weight a x.1.1 + weight a x.1.2 + weight a x.2

omit [Fintype ι] [DecidableEq ι] in
theorem occurrences_card (L : RepresentationLeaf ι) :
    L.occurrences.card = L.top.card.choose L.topCount *
      L.mixer.card.choose L.localCount * 2 ^ L.background.card := by
  simp [occurrences]

omit [Fintype ι] [DecidableEq ι] in
theorem occurrence_subsets (L : RepresentationLeaf ι) {x : Occurrence ι}
    (hx : x ∈ L.occurrences) :
    x.1.1 ⊆ L.top ∧ x.1.2 ⊆ L.mixer ∧ x.2 ⊆ L.background := by
  obtain ⟨htl, hb⟩ := Finset.mem_product.mp hx
  obtain ⟨ht, hl⟩ := Finset.mem_product.mp htl
  exact ⟨(Finset.mem_powersetCard.mp ht).1, (Finset.mem_powersetCard.mp hl).1,
    Finset.mem_powerset.mp hb⟩

end RepresentationLeaf

namespace RepresentationUniverse

abbrev ChildOccurrence (ι : Type*) :=
  RepresentationLeaf.Occurrence ι × RepresentationLeaf.Occurrence ι
abbrev ParentOccurrence (ι : Type*) := ChildOccurrence ι × ChildOccurrence ι

def children (L : Fin 4 → RepresentationLeaf ι) (j : Fin 2) : Finset (ChildOccurrence ι) :=
  (L ⟨2 * j.val, by omega⟩).occurrences ×ˢ (L ⟨2 * j.val + 1, by omega⟩).occurrences

def parents (L : Fin 4 → RepresentationLeaf ι) : Finset (ParentOccurrence ι) :=
  children L 0 ×ˢ children L 1

def childWeight (a : ι → ℤ) (x : ChildOccurrence ι) : ℤ :=
  RepresentationLeaf.occurrenceWeight a x.1 + RepresentationLeaf.occurrenceWeight a x.2

def parentWeight (a : ι → ℤ) (x : ParentOccurrence ι) : ℤ :=
  childWeight a x.1 + childWeight a x.2

def topMask (x : ParentOccurrence ι) : Finset ι :=
  ((x.1.1.1.1 ∪ x.1.2.1.1) ∪ x.2.1.1.1) ∪ x.2.2.1.1

def localMask (x : ParentOccurrence ι) : Finset ι :=
  ((x.1.1.1.2 ∪ x.1.2.1.2) ∪ x.2.1.1.2) ∪ x.2.2.1.2

def backgroundMask (x : ParentOccurrence ι) : Finset ι :=
  ((x.1.1.2 ∪ x.1.2.2) ∪ x.2.1.2) ∪ x.2.2.2

/-- Four selections are disjoint in their natural union order. -/
def DisjointFour (A B C D : Finset ι) : Prop :=
  Disjoint A B ∧ Disjoint (A ∪ B) C ∧ Disjoint ((A ∪ B) ∪ C) D

/-- Actual validity tests reject local overlap. Top and background disjointness
are automatic from the layout, and are stated here to expose the invariant. -/
def Valid (x : ParentOccurrence ι) : Prop :=
  DisjointFour x.1.1.1.1 x.1.2.1.1 x.2.1.1.1 x.2.2.1.1 ∧
  DisjointFour x.1.1.1.2 x.1.2.1.2 x.2.1.1.2 x.2.2.1.2 ∧
  DisjointFour x.1.1.2 x.1.2.2 x.2.1.2 x.2.2.2

private theorem weight_four (a : ι → ℤ) (A B C D : Finset ι)
    (h : DisjointFour A B C D) :
    weight a (((A ∪ B) ∪ C) ∪ D) = weight a A + weight a B + weight a C + weight a D := by
  rw [weight_union a h.2.2, weight_union a h.2.1, weight_union a h.1]

theorem valid_weight (a : ι → ℤ) {x : ParentOccurrence ι} (hx : Valid x) :
    parentWeight a x = weight a (topMask x) + weight a (localMask x) +
      weight a (backgroundMask x) := by
  rw [topMask, localMask, backgroundMask, weight_four a _ _ _ _ hx.1,
    weight_four a _ _ _ _ hx.2.1, weight_four a _ _ _ _ hx.2.2]
  simp only [parentWeight, childWeight, RepresentationLeaf.occurrenceWeight]
  ring

def entry (a : ι → ℤ) (x : ParentOccurrence ι) : Entry ι :=
  ⟨parentWeight a x, topMask x⟩

noncomputable def validEntries (a : ι → ℤ) (L : Fin 4 → RepresentationLeaf ι) :
    Finset (Entry ι) := by
  classical
  exact ((parents L).filter Valid).image (entry a)

omit [Fintype ι] [DecidableEq ι] in
theorem children_card (L : Fin 4 → RepresentationLeaf ι) (j : Fin 2) :
    (children L j).card = (L ⟨2 * j.val, by omega⟩).occurrences.card *
      (L ⟨2 * j.val + 1, by omega⟩).occurrences.card := by
  simp [children]

omit [Fintype ι] [DecidableEq ι] in
theorem parents_card (L : Fin 4 → RepresentationLeaf ι) :
    (parents L).card = (children L 0).card * (children L 1).card := by
  simp [parents]

/-- The counting target has one key per top mask, background subset and
local distinct weight, independent of the number of raw representations. -/
def entryFromParts (a : ι → ℤ) (x : (Finset ι × Finset ι) × ℤ) : Entry ι :=
  ⟨weight a x.1.1 + weight a x.1.2 + x.2, x.1.1⟩

noncomputable def entryEnvelope (a : ι → ℤ) (top background mixer : Finset ι) (k : ℕ) :
    Finset (Entry ι) :=
  ((top.powersetCard k ×ˢ background.powerset) ×ˢ distinctSums a mixer).image (entryFromParts a)

theorem entryEnvelope_card (a : ι → ℤ) (top background mixer : Finset ι) (k : ℕ) :
    (entryEnvelope a top background mixer k).card ≤
      top.card.choose k * 2 ^ background.card * distinctSumCount a mixer := by
  apply (Finset.card_image_le).trans
  simp [Finset.card_product, distinctSumCount]

theorem validEntries_card (a : ι → ℤ) (L : Fin 4 → RepresentationLeaf ι)
    (top background mixer : Finset ι) (k : ℕ)
    (ht : ∀ x ∈ parents L, topMask x ⊆ top ∧ (topMask x).card = k)
    (hb : ∀ x ∈ parents L, backgroundMask x ⊆ background)
    (hl : ∀ x ∈ parents L, localMask x ⊆ mixer) :
    (validEntries a L).card ≤
      top.card.choose k * 2 ^ background.card * distinctSumCount a mixer := by
  apply (Finset.card_le_card (show validEntries a L ⊆ entryEnvelope a top background mixer k from ?_)).trans
    (entryEnvelope_card a top background mixer k)
  classical
  intro e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hx, hv⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_image.mpr
  refine ⟨((topMask x, backgroundMask x), weight a (localMask x)), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr (ht x hx),
      Finset.mem_powerset.mpr (hb x hx)⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨localMask x, Finset.mem_powerset.mpr (hl x hx), rfl⟩
  · have hw := valid_weight a hv
    simp only [entryFromParts, entry]
    congr 1
    linarith


omit [Fintype ι] [DecidableEq ι] in
theorem mem_parents (L : Fin 4 → RepresentationLeaf ι) (x : ParentOccurrence ι) :
    x ∈ parents L ↔ x.1.1 ∈ (L 0).occurrences ∧ x.1.2 ∈ (L 1).occurrences ∧
      x.2.1 ∈ (L 2).occurrences ∧ x.2.2 ∈ (L 3).occurrences := by
  simp [parents, children, and_assoc]

def topDomain (L : Fin 4 → RepresentationLeaf ι) : Finset ι :=
  (((L 0).top ∪ (L 1).top) ∪ (L 2).top) ∪ (L 3).top

def mixerDomain (L : Fin 4 → RepresentationLeaf ι) : Finset ι :=
  (((L 0).mixer ∪ (L 1).mixer) ∪ (L 2).mixer) ∪ (L 3).mixer

def backgroundDomain (L : Fin 4 → RepresentationLeaf ι) : Finset ι :=
  (((L 0).background ∪ (L 1).background) ∪ (L 2).background) ∪ (L 3).background

omit [Fintype ι] in
theorem parent_part_subsets (L : Fin 4 → RepresentationLeaf ι) {x : ParentOccurrence ι}
    (hx : x ∈ parents L) :
    topMask x ⊆ topDomain L ∧ localMask x ⊆ mixerDomain L ∧
      backgroundMask x ⊆ backgroundDomain L := by
  obtain ⟨h0, h1, h2, h3⟩ := (mem_parents L x).mp hx
  have h0 := (L 0).occurrence_subsets h0
  have h1 := (L 1).occurrence_subsets h1
  have h2 := (L 2).occurrence_subsets h2
  have h3 := (L 3).occurrence_subsets h3
  exact ⟨Finset.union_subset_union (Finset.union_subset_union
      (Finset.union_subset_union h0.1 h1.1) h2.1) h3.1,
    Finset.union_subset_union (Finset.union_subset_union
      (Finset.union_subset_union h0.2.1 h1.2.1) h2.2.1) h3.2.1,
    Finset.union_subset_union (Finset.union_subset_union
      (Finset.union_subset_union h0.2.2 h1.2.2) h2.2.2) h3.2.2⟩

omit [Fintype ι] in
theorem topMask_card (L : Fin 4 → RepresentationLeaf ι)
    (ht : DisjointFour (L 0).top (L 1).top (L 2).top (L 3).top)
    {x : ParentOccurrence ι} (hx : x ∈ parents L) :
    (topMask x).card = (L 0).topCount + (L 1).topCount + (L 2).topCount + (L 3).topCount := by
  obtain ⟨h0, h1, h2, h3⟩ := (mem_parents L x).mp hx
  have s0 := (L 0).occurrence_subsets h0
  have s1 := (L 1).occurrence_subsets h1
  have s2 := (L 2).occurrence_subsets h2
  have s3 := (L 3).occurrence_subsets h3
  have c0 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp (Finset.mem_product.mp h0).1).1).2
  have c1 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp (Finset.mem_product.mp h1).1).1).2
  have c2 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp (Finset.mem_product.mp h2).1).1).2
  have c3 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp (Finset.mem_product.mp h3).1).1).2
  have d01 := ht.1.mono s0.1 s1.1
  have d012 := ht.2.1.mono (Finset.union_subset_union s0.1 s1.1) s2.1
  have d0123 := ht.2.2.mono
    (Finset.union_subset_union (Finset.union_subset_union s0.1 s1.1) s2.1) s3.1
  simp only [topMask, Finset.card_union_of_disjoint d0123,
    Finset.card_union_of_disjoint d012, Finset.card_union_of_disjoint d01, c0, c1, c2, c3]

/-- No entry-count premise: this follows directly from leaf domains and choices. -/
theorem concrete_validEntries_card (a : ι → ℤ) (L : Fin 4 → RepresentationLeaf ι)
    (ht : DisjointFour (L 0).top (L 1).top (L 2).top (L 3).top) :
    (validEntries a L).card ≤
      (topDomain L).card.choose ((L 0).topCount + (L 1).topCount +
        (L 2).topCount + (L 3).topCount) * 2 ^ (backgroundDomain L).card *
          distinctSumCount a (mixerDomain L) :=
  validEntries_card a L _ _ _ _
    (fun _ hx => ⟨(parent_part_subsets L hx).1, topMask_card L ht hx⟩)
    (fun _ hx => (parent_part_subsets L hx).2.2)
    (fun _ hx => (parent_part_subsets L hx).2.1)

end RepresentationUniverse



namespace RepresentationMoments

noncomputable def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card Ω

theorem mean_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    mean (fun _ : Ω => c) = c := by
  have h : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, h]

theorem mean_prod {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ] (f : Ω × Ψ → ℝ) :
    mean f = mean (fun x => mean (fun y => f (x, y))) := by
  simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    Finset.sum_div, div_div, mul_comm]

theorem mean_equiv {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ] (e : Ω ≃ Ψ) (f : Ψ → ℝ) :
    mean (fun x => f (e x)) = mean f := by
  rw [mean, mean, Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem mean_residue {α : Type*} (X : Finset α) (w : α → ℤ) {p : ℕ} (hp : 0 < p) :
    mean (fun r => ((residueFiltered hp X w r).card : ℝ)) = (X.card : ℝ) / p := by
  simpa only [mean, Fintype.card_fin] using mean_residueFiltered hp X w

theorem mean_residue_complement {α : Type*} (X : Finset α) (w : α → ℤ)
    {p : ℕ} (hp : 0 < p) (t : ℤ) :
    mean (fun r => ((residueFiltered hp X w (ResidueMatchAccounting.complement hp t r)).card : ℝ)) =
      (X.card : ℝ) / p := by
  exact (mean_equiv (ResidueMatchAccounting.complementEquiv hp t)
    (fun r => ((residueFiltered hp X w r).card : ℝ))).trans (mean_residue X w hp)

theorem mean_two_residues {α : Type*} (X : Finset α) (parent child : α → ℤ)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    mean (fun r : Fin p × Fin q => ((twiceResidueFiltered hp hq X parent child r).card : ℝ)) =
      (X.card : ℝ) / (p * q : ℕ) :=
  by simpa only [mean, Fintype.card_prod, Fintype.card_fin] using
    mean_twiceResidueFiltered hp hq X parent child

variable {p0 pL pR : ℕ} (h0 : 0 < p0) (hL : 0 < pL) (hR : 0 < pR)

abbrev Residues (p0 pL pR : ℕ) := Fin p0 × Fin pL × Fin pR

noncomputable def G (a : ι → ℤ) (L R : Fin 4 → RepresentationLeaf ι) (t : ℤ)
    (r : Residues p0 pL pR) : ℕ :=
  (residueFiltered hL (RepresentationUniverse.children L 0)
    (RepresentationUniverse.childWeight a) r.2.1).card +
  (residueFiltered hL (RepresentationUniverse.children L 1)
    (RepresentationUniverse.childWeight a)
      (ResidueMatchAccounting.complement hL r.1.val r.2.1)).card +
  (residueFiltered hR (RepresentationUniverse.children R 0)
    (RepresentationUniverse.childWeight a) r.2.2).card +
  (residueFiltered hR (RepresentationUniverse.children R 1)
    (RepresentationUniverse.childWeight a)
      (ResidueMatchAccounting.complement hR (t - r.1.val) r.2.2)).card

noncomputable def JL (a : ι → ℤ) (L : Fin 4 → RepresentationLeaf ι)
    (r : Residues p0 pL pR) : ℕ :=
  (twiceResidueFiltered h0 hL (RepresentationUniverse.parents L)
    (RepresentationUniverse.parentWeight a)
    (fun x => RepresentationUniverse.childWeight a x.1) (r.1, r.2.1)).card

noncomputable def JR (a : ι → ℤ) (R : Fin 4 → RepresentationLeaf ι) (t : ℤ)
    (r : Residues p0 pL pR) : ℕ :=
  (twiceResidueFiltered h0 hR (RepresentationUniverse.parents R)
    (RepresentationUniverse.parentWeight a)
    (fun x => RepresentationUniverse.childWeight a x.1)
    (ResidueMatchAccounting.complement h0 t r.1, r.2.2)).card

noncomputable def UL (a : ι → ℤ) (L : Fin 4 → RepresentationLeaf ι)
    (r : Residues p0 pL pR) : ℕ :=
  (residueFiltered h0 (RepresentationUniverse.validEntries a L) Entry.value r.1).card

noncomputable def UR (a : ι → ℤ) (R : Fin 4 → RepresentationLeaf ι) (t : ℤ)
    (r : Residues p0 pL pR) : ℕ :=
  (residueFiltered h0 (RepresentationUniverse.validEntries a R) Entry.value
    (ResidueMatchAccounting.complement h0 t r.1)).card

include h0 hL hR in
/-- All four child residues have the stated marginal laws, including the two
complementary residues depending on the independently chosen parent residue. -/
theorem mean_G (a : ι → ℤ) (L R : Fin 4 → RepresentationLeaf ι) (t : ℤ) :
    mean (fun r : Residues p0 pL pR => (G hL hR a L R t r : ℝ)) =
      ((RepresentationUniverse.children L 0).card + (RepresentationUniverse.children L 1).card : ℝ) / pL +
      ((RepresentationUniverse.children R 0).card + (RepresentationUniverse.children R 1).card : ℝ) / pR := by
  let : Nonempty (Fin p0) := ⟨⟨0, h0⟩⟩
  let : Nonempty (Fin pL) := ⟨⟨0, hL⟩⟩
  let : Nonempty (Fin pR) := ⟨⟨0, hR⟩⟩
  unfold G
  simp only [Nat.cast_add, mean_add]
  rw [mean_prod, mean_prod, mean_prod, mean_prod]
  simp_rw [mean_prod, mean_const, mean_residue, mean_residue_complement]
  simp only [mean_const]
  ring

include h0 hL hR in
theorem mean_JL (a : ι → ℤ) (L : Fin 4 → RepresentationLeaf ι) :
    mean (fun r : Residues p0 pL pR => (JL h0 hL a L r : ℝ)) =
      ((RepresentationUniverse.parents L).card : ℝ) / (p0 * pL : ℕ) := by
  let : Nonempty (Fin pR) := ⟨⟨0, hR⟩⟩
  unfold JL
  rw [mean_prod]
  simp_rw [mean_prod, mean_const]
  exact (mean_prod (fun r : Fin p0 × Fin pL =>
    ((twiceResidueFiltered h0 hL (RepresentationUniverse.parents L)
      (RepresentationUniverse.parentWeight a)
      (fun x => RepresentationUniverse.childWeight a x.1) r).card : ℝ))).symm.trans
        (mean_two_residues _ _ _ h0 hL)

include h0 hL hR in
theorem mean_JR (a : ι → ℤ) (R : Fin 4 → RepresentationLeaf ι) (t : ℤ) :
    mean (fun r : Residues p0 pL pR => (JR h0 hR a R t r : ℝ)) =
      ((RepresentationUniverse.parents R).card : ℝ) / (p0 * pR : ℕ) := by
  let : Nonempty (Fin pL) := ⟨⟨0, hL⟩⟩
  unfold JR
  rw [mean_prod]
  simp_rw [mean_prod, mean_const]
  have he := mean_equiv
    (Equiv.prodCongr (ResidueMatchAccounting.complementEquiv h0 t) (Equiv.refl (Fin pR)))
    (fun r : Fin p0 × Fin pR => ((twiceResidueFiltered h0 hR
      (RepresentationUniverse.parents R) (RepresentationUniverse.parentWeight a)
      (fun x => RepresentationUniverse.childWeight a x.1) r).card : ℝ))
  exact (mean_prod (fun r : Fin p0 × Fin pR =>
    ((twiceResidueFiltered h0 hR (RepresentationUniverse.parents R)
      (RepresentationUniverse.parentWeight a)
      (fun x => RepresentationUniverse.childWeight a x.1)
      (ResidueMatchAccounting.complement h0 t r.1, r.2)).card : ℝ))).symm.trans
        (he.trans (mean_two_residues _ _ _ h0 hR))

include h0 hL hR in
theorem mean_UL (a : ι → ℤ) (L : Fin 4 → RepresentationLeaf ι) :
    mean (fun r : Residues p0 pL pR => (UL h0 a L r : ℝ)) =
      ((RepresentationUniverse.validEntries a L).card : ℝ) / p0 := by
  let : Nonempty (Fin pL × Fin pR) := ⟨⟨⟨0, hL⟩, ⟨0, hR⟩⟩⟩
  unfold UL
  rw [mean_prod]
  simp_rw [mean_const]
  exact mean_residue _ _ h0

include h0 hL hR in
theorem mean_UR (a : ι → ℤ) (R : Fin 4 → RepresentationLeaf ι) (t : ℤ) :
    mean (fun r : Residues p0 pL pR => (UR h0 a R t r : ℝ)) =
      ((RepresentationUniverse.validEntries a R).card : ℝ) / p0 := by
  let : Nonempty (Fin pL × Fin pR) := ⟨⟨⟨0, hL⟩, ⟨0, hR⟩⟩⟩
  unfold UR
  rw [mean_prod]
  simp_rw [mean_const]
  exact mean_residue_complement _ _ h0 t



theorem count_tail {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (count : Ω → ℕ) {T : ℝ} (hT : 0 < T) :
    finiteUniformProbability (fun r => T < (count r : ℝ)) ≤
      mean (fun r => (count r : ℝ)) / T := by
  classical
  simpa only [finiteUniformProbability, Fintype.card_subtype, mean] using
    finite_count_markov count hT

private theorem scale_ratio {u X : ℝ} (hu : 0 < u) (hX : 0 < X) {a b : ℕ}
    (hab : a ≤ b) : (u ^ a * X) / (u ^ b * X) = 1 / u ^ (b - a) := by
  have he : u ^ b = u ^ a * u ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_of_le hab]
  rw [he]
  field_simp

/-- The resource event is determined before the extra prime, prefixes, or
separating families. Counts are taken on raw occurrences or actual entry keys. -/
def GoodResource (a : ι → ℤ) (L R : Fin 4 → RepresentationLeaf ι) (t : ℤ)
    (u gamma lambda halfN : ℝ) (r : Residues p0 pL pR) : Prop :=
  (G hL hR a L R t r : ℝ) ≤ u ^ 200 * (2 : ℝ) ^ gamma ∧
  ((JL h0 hL a L r + JR h0 hR a R t r : ℕ) : ℝ) ≤ u ^ 200 * (2 : ℝ) ^ halfN ∧
  (UL h0 a L r : ℝ) ≤ u ^ 200 * (2 : ℝ) ^ lambda ∧
  (UR h0 a R t r : ℝ) ≤ u ^ 200 * (2 : ℝ) ^ lambda

/-- The hypotheses are deterministic finite universe bounds, not moment or
trial-success assumptions. The moments themselves are the exact identities above. -/
theorem resource_failure_le (a : ι → ℤ) (L R : Fin 4 → RepresentationLeaf ι) (t : ℤ)
    (u gamma lambda halfN : ℝ) (hu : 0 < u)
    (hG : ((RepresentationUniverse.children L 0).card + (RepresentationUniverse.children L 1).card : ℝ) / pL +
      ((RepresentationUniverse.children R 0).card + (RepresentationUniverse.children R 1).card : ℝ) / pR ≤
        u ^ 26 * (2 : ℝ) ^ gamma)
    (hJ : ((RepresentationUniverse.parents L).card : ℝ) / (p0 * pL : ℕ) +
      ((RepresentationUniverse.parents R).card : ℝ) / (p0 * pR : ℕ) ≤
        u ^ 51 * (2 : ℝ) ^ halfN)
    (hUL : ((RepresentationUniverse.validEntries a L).card : ℝ) / p0 ≤
      u ^ 10 * (2 : ℝ) ^ lambda)
    (hUR : ((RepresentationUniverse.validEntries a R).card : ℝ) / p0 ≤
      u ^ 10 * (2 : ℝ) ^ lambda) :
    finiteUniformProbability (fun r : Residues p0 pL pR => ¬GoodResource h0 hL hR a L R t u gamma lambda halfN r) ≤
      1 / u ^ 174 + 1 / u ^ 149 + 2 / u ^ 190 := by
  let : Nonempty (Fin p0) := ⟨⟨0, h0⟩⟩
  let : Nonempty (Fin pL) := ⟨⟨0, hL⟩⟩
  let : Nonempty (Fin pR) := ⟨⟨0, hR⟩⟩
  have g := (count_tail (fun r : Residues p0 pL pR => G hL hR a L R t r)
    (show 0 < u ^ 200 * (2 : ℝ) ^ gamma by positivity)).trans
      (div_le_div_of_nonneg_right ((mean_G h0 hL hR a L R t).le.trans hG) (by positivity))
  have j := (count_tail (fun r : Residues p0 pL pR => JL h0 hL a L r + JR h0 hR a R t r)
    (show 0 < u ^ 200 * (2 : ℝ) ^ halfN by positivity)).trans
      (div_le_div_of_nonneg_right (show mean (fun r : Residues p0 pL pR => ((JL h0 hL a L r + JR h0 hR a R t r : ℕ) : ℝ)) ≤
        u ^ 51 * (2 : ℝ) ^ halfN by
          simpa only [Nat.cast_add, mean_add, mean_JL h0 hL hR, mean_JR h0 hL hR] using hJ)
        (by positivity))
  have l := (count_tail (fun r : Residues p0 pL pR => UL h0 a L r)
    (show 0 < u ^ 200 * (2 : ℝ) ^ lambda by positivity)).trans
      (div_le_div_of_nonneg_right ((mean_UL h0 hL hR a L).le.trans hUL) (by positivity))
  have r := (count_tail (fun r : Residues p0 pL pR => UR h0 a R t r)
    (show 0 < u ^ 200 * (2 : ℝ) ^ lambda by positivity)).trans
      (div_le_div_of_nonneg_right ((mean_UR h0 hL hR a R t).le.trans hUR) (by positivity))
  rw [scale_ratio hu (by positivity) (by omega : 26 ≤ 200)] at g
  rw [scale_ratio hu (by positivity) (by omega : 51 ≤ 200)] at j
  rw [scale_ratio hu (by positivity) (by omega : 10 ≤ 200)] at l r
  have hsplit : (fun r : Residues p0 pL pR => ¬GoodResource h0 hL hR a L R t u gamma lambda halfN r) =
      (fun r : Residues p0 pL pR => u ^ 200 * (2 : ℝ) ^ gamma < (G hL hR a L R t r : ℝ) ∨
        u ^ 200 * (2 : ℝ) ^ halfN < ((JL h0 hL a L r + JR h0 hR a R t r : ℕ) : ℝ) ∨
        u ^ 200 * (2 : ℝ) ^ lambda < (UL h0 a L r : ℝ) ∨
        u ^ 200 * (2 : ℝ) ^ lambda < (UR h0 a R t r : ℝ)) := by
    funext r
    simp only [GoodResource, not_and_or, not_le]
  rw [hsplit]
  have h := finiteUniformProbability_union_le
    (fun r : Residues p0 pL pR => u ^ 200 * (2 : ℝ) ^ gamma < (G hL hR a L R t r : ℝ))
    (fun r : Residues p0 pL pR => u ^ 200 * (2 : ℝ) ^ halfN < ((JL h0 hL a L r + JR h0 hR a R t r : ℕ) : ℝ) ∨
      u ^ 200 * (2 : ℝ) ^ lambda < (UL h0 a L r : ℝ) ∨
      u ^ 200 * (2 : ℝ) ^ lambda < (UR h0 a R t r : ℝ))
  have h2 := finiteUniformProbability_union_le
    (fun r : Residues p0 pL pR => u ^ 200 * (2 : ℝ) ^ halfN < ((JL h0 hL a L r + JR h0 hR a R t r : ℕ) : ℝ))
    (fun r : Residues p0 pL pR => u ^ 200 * (2 : ℝ) ^ lambda < (UL h0 a L r : ℝ) ∨
      u ^ 200 * (2 : ℝ) ^ lambda < (UR h0 a R t r : ℝ))
  have h3 := finiteUniformProbability_union_le
    (fun r : Residues p0 pL pR => u ^ 200 * (2 : ℝ) ^ lambda < (UL h0 a L r : ℝ))
    (fun r : Residues p0 pL pR => u ^ 200 * (2 : ℝ) ^ lambda < (UR h0 a R t r : ℝ))
  norm_num only [Nat.reduceSub] at g j l r
  rw [show 2 / u ^ 190 = 1 / u ^ 190 + 1 / u ^ 190 by ring]
  linarith

private theorem reciprocal_pow_small {u : ℝ} (hu : 2 ≤ u) (k : ℕ) (hk : 107 ≤ k) :
    1 / u ^ k ≤ 1 / (128 * u ^ 100) := by
  have hu0 : 0 < u := by linarith
  have h7 : (128 : ℝ) ≤ u ^ 7 := by
    convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hu 7 using 1
    norm_num
  have hp : u ^ 7 ≤ u ^ (k - 100) :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ u) (by omega)
  have he : u ^ k = u ^ 100 * u ^ (k - 100) := by rw [← pow_add, Nat.add_sub_of_le (by omega : 100 ≤ k)]
  apply one_div_le_one_div_of_le (by positivity)
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left (h7.trans hp) (pow_nonneg hu0.le 100)]

theorem resource_failure_small {u : ℝ} (hu : 2 ≤ u) :
    1 / u ^ 174 + 1 / u ^ 149 + 2 / u ^ 190 < (1 / 10 : ℝ) / u ^ 100 := by
  have hu0 : 0 < u := by linarith
  have h1 := reciprocal_pow_small hu 174 (by omega)
  have h2 := reciprocal_pow_small hu 149 (by omega)
  have h3 := reciprocal_pow_small hu 190 (by omega)
  have hpos : 0 < u ^ 100 := by positivity
  have hstrict : 4 / (128 * u ^ 100) < (1 / 10 : ℝ) / u ^ 100 := by
    field_simp
    nlinarith
  have he : 2 / u ^ 190 = 2 * (1 / u ^ 190) := by ring
  rw [he]
  apply lt_of_le_of_lt _ hstrict
  calc
    _ ≤ 1 / (128 * u ^ 100) + 1 / (128 * u ^ 100) + 2 * (1 / (128 * u ^ 100)) := by
      linarith
    _ = _ := by ring


/-- Averaging conditional failure bounds preserves a joint bound with the
passing event. No conditioning on the rare survival event is performed. -/
theorem joint_failure_average {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (Ψ : Ω → Type*) [∀ x, Fintype (Ψ x)] [∀ x, Nonempty (Ψ x)]
    (passing : Ω → Prop) (bad : ∀ x, Ψ x → Prop) {delta : ℝ} (hd : 0 ≤ delta)
    (hb : ∀ x, passing x → finiteUniformProbability (bad x) ≤ delta) :
    (μ.bind Ψ (fun _ => FiniteLaw.uniform)).probability
      (fun x => passing x.1 ∧ bad x.1 x.2) ≤ delta := by
  classical
  rw [FiniteLaw.bind_probability]
  calc
    _ ≤ ∑ x, μ.mass x * delta := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : passing x
      · simp only [hx, true_and, FiniteLaw.uniform_probability]
        exact mul_le_mul_of_nonneg_left (hb x hx) (μ.nonneg x)
      · simp only [hx, false_and, FiniteLaw.probability, ↓reduceIte, Finset.sum_const_zero, mul_zero]
        exact mul_nonneg (μ.nonneg x) hd
    _ = delta := by rw [← Finset.sum_mul, μ.total, one_mul]

end RepresentationMoments

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

/-- The exact labeled block supplied by the sampled partition. -/
noncomputable def rawPartitionBlock (z : Layout n) (f : R.Partitions z)
    (j : Fin 3) (a : ℕ) : Finset (Fin n) :=
  (R.orderedMixers z j).filter fun x =>
    ∃ hx : x ∈ R.orderedMixers z j, ((f j).val ⟨x, hx⟩).val = a

theorem rawPartitionBlock_subset (z : Layout n) (f : R.Partitions z) (j : Fin 3) (a : ℕ) :
    R.rawPartitionBlock z f j a ⊆ R.orderedMixers z j := Finset.filter_subset _ _

theorem rawPartitionBlock_disjoint (z : Layout n) (f : R.Partitions z) (j : Fin 3)
    {a b : ℕ} (hab : a ≠ b) :
    Disjoint (R.rawPartitionBlock z f j a) (R.rawPartitionBlock z f j b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hx, ha, hax⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy, hb, hbx⟩ := Finset.mem_filter.mp hy
  exact hab (hax.symm.trans hbx)

/-- Eight disjoint background allocations in a fixed order. This uses all
outside indices, regardless of which ones belong to the fixed solution. -/
def rawBackground (z : Layout n) (B : Fin n → Fin 2 × Fin 4)
    (j : Fin 2) (i : Fin 4) : Finset (Fin n) :=
  (Finset.univ \ R.mixerUnion z).filter fun x => B x = (j, i)

/-- Table 1's actual leaf domains and rounded prescribed counts. -/
noncomputable def rawLeaf (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) (i : Fin 4) : RepresentationLeaf (Fin n) where
  top := R.rawPartitionBlock z f 0 i.val
  mixer := R.rawPartitionBlock z f j.succ (i.val % 2)
  background := R.rawBackground z B j i
  topCount := if j = 0 then balancedBlockCounts 4 (g 0).val i
    else blockHalf n 0 - balancedBlockCounts 4 (g 0).val i
  localCount := if i.val < 2 then balancedBlockCounts 2 (g j.succ).val ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
    else blockHalf n j.succ - balancedBlockCounts 2 (g j.succ).val ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩

theorem rawLeaf_top_disjoint (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) :
    RepresentationUniverse.DisjointFour (R.rawLeaf z g f B j 0).top
      (R.rawLeaf z g f B j 1).top (R.rawLeaf z g f B j 2).top
      (R.rawLeaf z g f B j 3).top := by
  classical
  dsimp [rawLeaf, RepresentationUniverse.DisjointFour]
  refine ⟨R.rawPartitionBlock_disjoint z f 0 (by decide), ?_, ?_⟩
  · exact Finset.disjoint_union_left.mpr
      ⟨R.rawPartitionBlock_disjoint z f 0 (by decide),
       R.rawPartitionBlock_disjoint z f 0 (by decide)⟩
  · exact Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr
        ⟨R.rawPartitionBlock_disjoint z f 0 (by decide),
         R.rawPartitionBlock_disjoint z f 0 (by decide)⟩,
       R.rawPartitionBlock_disjoint z f 0 (by decide)⟩

theorem rawLeaf_validEntries_card (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) :
    let L := R.rawLeaf z g f B j
    (RepresentationUniverse.validEntries (R.signedWeights z) L).card ≤
      (RepresentationUniverse.topDomain L).card.choose
        ((L 0).topCount + (L 1).topCount + (L 2).topCount + (L 3).topCount) *
      2 ^ (RepresentationUniverse.backgroundDomain L).card *
        distinctSumCount (R.signedWeights z) (RepresentationUniverse.mixerDomain L) :=
  RepresentationUniverse.concrete_validEntries_card _ _ (R.rawLeaf_top_disjoint z g f B j)

end RepresentationSetup

end LowSpaceSubsetSum

end

end OAI
