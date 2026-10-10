import OAI.Combinatorics.FiniteCircle.Edit

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

def segment {α : Type*} (x : List α) (start size : ℕ) : List α := (x.drop start).take size

theorem segment_sublist {α : Type*} (x : List α) (start size : ℕ) :
    segment x start size <+ x := (List.take_sublist _ _).trans (List.drop_sublist _ _)

theorem length_segment {α : Type*} {x : List α} {start size : ℕ}
    (h : start + size ≤ x.length) : (segment x start size).length = size := by
  simp only [segment, List.length_take, List.length_drop]
  omega

theorem unequalDeficit_segment_sublist_le {α : Type*} {x y : List α} (h : x <+ y)
    (start size : ℕ) :
    unequalDeficit (segment x start size) (segment y start size) ≤ y.length - x.length := by
  have hl := h.length_le
  exact (unequalDeficit_take_sublist_le (h.drop start) size).trans (by
    simp only [List.length_drop]
    omega)

theorem unequalDeficit_symm {α : Type*} (x y : List α) :
    unequalDeficit x y = unequalDeficit y x := by
  simp [unequalDeficit, lcs_symm x y, max_comm]

inductive Slide {α : Type*} : List α → List α → Prop
  | forward (u v t : List α) (a b : α) :
      Slide (u ++ a :: (v ++ t)) (u ++ v ++ b :: t)
  | backward (u v t : List α) (a b : α) :
      Slide (u ++ v ++ b :: t) (u ++ a :: (v ++ t))

namespace Slide
variable {α : Type*} {x y : List α}

theorem symm (h : Slide x y) : Slide y x := by
  cases h with
  | forward u v t a b => exact .backward u v t a b
  | backward u v t a b => exact .forward u v t a b

theorem length_eq (h : Slide x y) : x.length = y.length := by
  cases h <;> simp <;> omega

theorem append_left (h : Slide x y) (l : List α) : Slide (l ++ x) (l ++ y) := by
  cases h with
  | forward u v t a b => simpa only [List.append_assoc] using Slide.forward (l ++ u) v t a b
  | backward u v t a b => simpa only [List.append_assoc] using Slide.backward (l ++ u) v t a b

theorem append_right (h : Slide x y) (l : List α) : Slide (x ++ l) (y ++ l) := by
  cases h with
  | forward u v t a b =>
    simpa only [List.append_assoc, List.cons_append] using Slide.forward u v (t ++ l) a b
  | backward u v t a b =>
    simpa only [List.append_assoc, List.cons_append] using Slide.backward u v (t ++ l) a b

theorem common_delete (h : Slide x y) :
    ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length + 1 = x.length ∧ z.length + 1 = y.length := by
  cases h with
  | forward u v t a b =>
    exact ⟨u ++ v ++ t,
      by simpa only [List.append_assoc] using ((List.Sublist.refl (v ++ t)).cons a).append_left u,
      ((List.Sublist.refl t).cons b).append_left (u ++ v), by simp; omega, by simp; omega⟩
  | backward u v t a b =>
    exact ⟨u ++ v ++ t,
      ((List.Sublist.refl t).cons b).append_left (u ++ v),
      by simpa only [List.append_assoc] using ((List.Sublist.refl (v ++ t)).cons a).append_left u,
      by simp; omega, by simp; omega⟩

theorem segment_deficit_le_two (h : Slide x y) (start size : ℕ) :
    unequalDeficit (segment x start size) (segment y start size) ≤ 2 := by
  obtain ⟨z, hx, hy, hzx, hzy⟩ := h.common_delete
  have hleft := unequalDeficit_segment_sublist_le hx start size
  have hright := unequalDeficit_segment_sublist_le hy start size
  rw [unequalDeficit_symm] at hleft
  exact (unequalDeficit_triangle _ (segment z start size) _).trans (by omega)
end Slide

inductive SlidePath {α : Type*} : ℕ → List α → List α → Prop
  | nil (x : List α) : SlidePath 0 x x
  | cons {n : ℕ} {x y z : List α} : Slide x y → SlidePath n y z → SlidePath (n + 1) x z

namespace SlidePath
variable {α : Type*} {x y z : List α} {n m : ℕ}

theorem trans (h : SlidePath n x y) (g : SlidePath m y z) : SlidePath (n + m) x z := by
  induction h with
  | nil => simpa using g
  | cons h hs ih => simpa only [Nat.add_right_comm] using SlidePath.cons h (ih g)

theorem symm (h : SlidePath n x y) : SlidePath n y x := by
  induction h with
  | nil x => exact .nil x
  | cons h hs ih => exact ih.trans (.cons h.symm (.nil _))

theorem append_left (h : SlidePath n x y) (l : List α) : SlidePath n (l ++ x) (l ++ y) := by
  induction h with
  | nil => exact .nil _
  | cons h hs ih => exact .cons (h.append_left l) ih

theorem append_right (h : SlidePath n x y) (l : List α) : SlidePath n (x ++ l) (y ++ l) := by
  induction h with
  | nil => exact .nil _
  | cons h hs ih => exact .cons (h.append_right l) ih

theorem length_eq (h : SlidePath n x y) : x.length = y.length := by
  induction h with
  | nil => rfl
  | cons h hs ih => exact h.length_eq.trans ih

theorem to_padded_sublist (h : z <+ x) (a : α) :
    SlidePath (x.length - z.length) x (z ++ List.replicate (x.length - z.length) a) := by
  induction h with
  | slnil => simpa using SlidePath.nil ([] : List α)
  | @cons z x b h ih =>
    have hl := h.length_le
    have hfirst : Slide (b :: x) (x ++ [a]) := by
      simpa using Slide.forward ([] : List α) x [] b a
    have ht := SlidePath.cons hfirst (ih.append_right [a])
    simpa only [List.length_cons,
      show x.length + 1 - z.length = (x.length - z.length) + 1 by omega,
      List.append_assoc, List.replicate_succ', List.concat_eq_append] using ht
  | cons_cons b h ih =>
    simpa using ih.append_left [b]
end SlidePath

theorem exists_slidePath {α : Type*} (a : α) {x y : List α} (h : x.length = y.length) :
    SlidePath (2 * deficit x y) x y := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
  have h1 := SlidePath.to_padded_sublist hx a
  have h2 := SlidePath.to_padded_sublist hy a
  rw [← h] at h2
  have ht := h1.trans h2.symm
  simpa only [deficit, hz, two_mul] using ht

structure WordMatching {α : Type*} (x y : List α) (q : ℕ) where
  left : Fin q ↪o Fin x.length
  right : Fin q ↪o Fin y.length
  letters : ∀ i, x.get (left i) = y.get (right i)

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem le_lcs (A : WordMatching x y q) : q ≤ lcs x y := by
  let z := List.ofFn (fun i : Fin q => x.get (A.left i))
  have hx : z <+ x := by
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    have he : z.length = q := List.length_ofFn
    refine ⟨(Fin.castOrderIso he).toOrderEmbedding.trans A.left, ?_⟩
    intro i
    change (List.ofFn (fun j : Fin q => x.get (A.left j))).get i = x.get (A.left (Fin.cast he i))
    rw [List.get_ofFn]
  have hy : z <+ y := by
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    have he : z.length = q := List.length_ofFn
    refine ⟨(Fin.castOrderIso he).toOrderEmbedding.trans A.right, ?_⟩
    intro i
    change (List.ofFn (fun j : Fin q => x.get (A.left j))).get i = y.get (A.right (Fin.cast he i))
    rw [List.get_ofFn]
    convert A.letters (Fin.cast he i) using 1
  simpa [z] using FiniteCircle.le_lcs hx hy

def restrict (A : WordMatching x y q) {r : ℕ} (e : Fin r ↪o Fin q) : WordMatching x y r where
  left := e.trans A.left
  right := e.trans A.right
  letters i := A.letters (e i)

def symm (A : WordMatching x y q) : WordMatching y x q where
  left := A.right
  right := A.left
  letters i := (A.letters i).symm

def rightSpan (A : WordMatching x y q) (S : Finset (Fin q)) : Finset (Fin y.length) :=
  Finset.univ.filter (fun j => ∃ i ∈ S, ∃ k ∈ S, A.right i ≤ j ∧ j ≤ A.right k)

theorem rightSpan_matched_iff (A : WordMatching x y q) (S : Finset (Fin q))
    (hS : ∀ i ∈ S, ∀ k ∈ S, ∀ j, i ≤ j → j ≤ k → j ∈ S) (j : Fin q) :
    A.right j ∈ A.rightSpan S ↔ j ∈ S := by
  simp only [rightSpan, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, k, hk, hij, hjk⟩
    exact hS i hi k hk j (A.right.le_iff_le.mp hij) (A.right.le_iff_le.mp hjk)
  · intro hj
    exact ⟨j, hj, j, hj, le_rfl, le_rfl⟩

theorem rightSpan_disjoint (A : WordMatching x y q) {S T : Finset (Fin q)}
    (h : ∀ i ∈ S, ∀ j ∈ T, i < j) : Disjoint (A.rightSpan S) (A.rightSpan T) := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  obtain ⟨_, i, hi, k, hk, hiz, hzk⟩ := Finset.mem_filter.mp hz
  obtain ⟨_, j, hj, l, hl, hjz, hzl⟩ := Finset.mem_filter.mp hw
  have hkj : A.right k < A.right j := A.right.strictMono (h k hk j hj)
  exact (not_lt_of_ge (hjz.trans hzk)) hkj

theorem sum_span_card_le {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : WordMatching x y q) (S : ι → Finset (Fin q))
    (h : ∀ i j, i < j → ∀ u ∈ S i, ∀ v ∈ S j, u < v) :
    ∑ i, (A.rightSpan (S i)).card ≤ y.length := by
  classical
  have hdis : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => A.rightSpan (S i)) := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact A.rightSpan_disjoint (h i j hij)
    · exact (A.rightSpan_disjoint (h j i hij)).symm
  rw [← Finset.card_biUnion hdis]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Fintype.card_fin _)

end WordMatching

theorem exists_lcs_matching {α : Type*} (x y : List α) :
    Nonempty (WordMatching x y (lcs x y)) := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hy
  let e := (Fin.castOrderIso hz.symm).toOrderEmbedding
  exact ⟨⟨e.trans f, e.trans g, fun i => (hf (e i)).symm.trans (hg (e i))⟩⟩

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

def sourceBlock (A : WordMatching x y q) (w i : ℕ) : Finset (Fin q) :=
  Finset.univ.filter (fun k => (A.left k).val / w = i)

@[simp] theorem mem_sourceBlock (A : WordMatching x y q) (w i : ℕ) (k : Fin q) :
    k ∈ A.sourceBlock w i ↔ (A.left k).val / w = i := by simp [sourceBlock]

theorem sourceBlock_card_le (A : WordMatching x y q) {w : ℕ} (hw : 0 < w) (i : ℕ) :
    (A.sourceBlock w i).card ≤ w := by
  let f : Fin q → Fin w := fun k => ⟨(A.left k).val % w, Nat.mod_lt _ hw⟩
  have h : Set.InjOn f (↑(A.sourceBlock w i) : Set (Fin q)) := by
    intro j hj k hk he
    apply A.left.injective
    apply Fin.ext
    have hj := (A.mem_sourceBlock w i j).mp hj
    have hk := (A.mem_sourceBlock w i k).mp hk
    have hf : (A.left j).val % w = (A.left k).val % w := congrArg Fin.val he
    have h1 := Nat.mod_add_div (A.left j).val w
    have h2 := Nat.mod_add_div (A.left k).val w
    rw [hj, hf] at h1
    rw [hk] at h2
    omega
  have hc := Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) h
  simpa using hc

theorem sum_sourceBlock_card (A : WordMatching x y q) {w L : ℕ} (hw : 0 < w)
    (hx : x.length = w*L) : ∑ i : Fin L, (A.sourceBlock w i).card = q := by
  let f : Fin q → Fin L := fun k => ⟨(A.left k).val / w, by
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    simpa only [hx, Nat.mul_comm] using (A.left k).isLt⟩
  have hh (i : Fin L) : A.sourceBlock w i = Finset.univ.filter (fun k => f k = i) := by
    ext k
    simp only [mem_sourceBlock, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, f]
  simp_rw [hh]
  simpa using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin q))
    (Finset.univ : Finset (Fin L)) f

theorem sourceBlock_order (A : WordMatching x y q) {w i j : ℕ} (hij : i < j)
    {k l : Fin q} (hk : k ∈ A.sourceBlock w i) (hl : l ∈ A.sourceBlock w j) : k < l := by
  by_contra h
  have hkl := A.left.monotone (not_lt.mp h)
  have hd := Nat.div_le_div_right (c := w) (show (A.left l).val ≤ (A.left k).val from hkl)
  rw [← (A.mem_sourceBlock w i k).mp hk, ← (A.mem_sourceBlock w j l).mp hl] at hij
  omega

theorem sourceBlock_convex (A : WordMatching x y q) (w i : ℕ) :
    ∀ k ∈ A.sourceBlock w i, ∀ l ∈ A.sourceBlock w i, ∀ j, k ≤ j → j ≤ l →
      j ∈ A.sourceBlock w i := by
  intro k hk l hl j hkj hjl
  rw [mem_sourceBlock] at *
  have h1 := Nat.div_le_div_right (c := w) (show (A.left k).val ≤ (A.left j).val from A.left.monotone hkj)
  have h2 := Nat.div_le_div_right (c := w) (show (A.left j).val ≤ (A.left l).val from A.left.monotone hjl)
  omega

theorem card_le_rightSpan (A : WordMatching x y q) (S : Finset (Fin q)) :
    S.card ≤ (A.rightSpan S).card := by
  have hmaps : Set.MapsTo A.right (↑S : Set (Fin q)) (↑(A.rightSpan S) : Set (Fin y.length)) := by
    intro k hk
    change A.right k ∈ A.rightSpan S
    simp only [rightSpan, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨k, hk, k, hk, le_rfl, le_rfl⟩
  exact Finset.card_le_card_of_injOn A.right hmaps A.right.injective.injOn

def sourceLoss (A : WordMatching x y q) (w i : ℕ) : ℕ := w - (A.sourceBlock w i).card

def spanLoss (A : WordMatching x y q) (w i : ℕ) : ℕ :=
  (A.rightSpan (A.sourceBlock w i)).card - (A.sourceBlock w i).card

theorem sum_sourceLoss (A : WordMatching x y q) {w L : ℕ} (hw : 0 < w)
    (hx : x.length = w*L) : ∑ i : Fin L, A.sourceLoss w i = w*L-q := by
  have he : (∑ i : Fin L, A.sourceLoss w i) + q = w*L := by
    conv_lhs => rhs; rw [← A.sum_sourceBlock_card hw hx]
    rw [← Finset.sum_add_distrib]
    simp only [sourceLoss, Nat.sub_add_cancel (A.sourceBlock_card_le hw _),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
  omega

theorem sum_spanLoss_le (A : WordMatching x y q) {w L : ℕ} (hw : 0 < w)
    (hx : x.length = w*L) (hy : y.length = w*L) : ∑ i : Fin L, A.spanLoss w i ≤ w*L-q := by
  have he : (∑ i : Fin L, A.spanLoss w i) + q =
      ∑ i : Fin L, (A.rightSpan (A.sourceBlock w i)).card := by
    conv_lhs => rhs; rw [← A.sum_sourceBlock_card hw hx]
    rw [← Finset.sum_add_distrib]
    simp only [spanLoss, Nat.sub_add_cancel (A.card_le_rightSpan _)]
  have hle := A.sum_span_card_le (fun i : Fin L => A.sourceBlock w i)
    (fun _ _ hij _ hk _ hl => A.sourceBlock_order hij hk hl)
  have hle' := hle.trans_eq hy
  omega

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

def ConvexIndices (S : Finset (Fin q)) : Prop :=
  ∀ i ∈ S, ∀ k ∈ S, ∀ j, i ≤ j → j ≤ k → j ∈ S

theorem rightSpan_mono (A : WordMatching x y q) {S T : Finset (Fin q)} (h : S ⊆ T) :
    A.rightSpan S ⊆ A.rightSpan T := by
  intro j hj
  obtain ⟨_, i, hi, k, hk, hij, hjk⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, h hi, k, h hk, hij, hjk⟩

theorem rightSpan_eq_Icc (A : WordMatching x y q) {S : Finset (Fin q)} (h : S.Nonempty) :
    A.rightSpan S = Finset.Icc (A.right (S.min' h)) (A.right (S.max' h)) := by
  ext j
  simp only [rightSpan, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, k, hk, hij, hjk⟩
    exact ⟨(A.right.monotone (S.min'_le _ hi)).trans hij,
      hjk.trans (A.right.monotone (S.le_max' _ hk))⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨_, S.min'_mem h, _, S.max'_mem h, hlo, hhi⟩

theorem convex_eq_Icc {S : Finset (Fin q)} (hS : ConvexIndices S) (h : S.Nonempty) :
    S = Finset.Icc (S.min' h) (S.max' h) := by
  ext j
  constructor
  · intro hj
    exact Finset.mem_Icc.mpr ⟨S.min'_le _ hj, S.le_max' _ hj⟩
  · intro hj
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hj
    exact hS _ (S.min'_mem h) _ (S.max'_mem h) j hlo hhi

theorem card_span_unmatched (A : WordMatching x y q) {S : Finset (Fin q)}
    (hS : ConvexIndices S) :
    (A.rightSpan S \ (Finset.univ.image A.right)).card = (A.rightSpan S).card - S.card := by
  have he : A.rightSpan S \ (Finset.univ.image A.right) = A.rightSpan S \ (S.image A.right) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj, hn⟩
      exact ⟨hj, fun ⟨k, _, hk⟩ => hn ⟨k, hk⟩⟩
    · rintro ⟨hj, hn⟩
      refine ⟨hj, ?_⟩
      rintro ⟨k, rfl⟩
      exact hn ⟨k, (A.rightSpan_matched_iff S hS k).mp hj, rfl⟩
  have hs : S.image A.right ⊆ A.rightSpan S := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact (A.rightSpan_matched_iff S hS k).mpr hk
  rw [he, Finset.card_sdiff_of_subset hs, Finset.card_image_of_injective S A.right.injective]

theorem span_holes_mono (A : WordMatching x y q) {S T : Finset (Fin q)}
    (hS : ConvexIndices S) (hT : ConvexIndices T) (h : S ⊆ T) :
    (A.rightSpan S).card - S.card ≤ (A.rightSpan T).card - T.card := by
  rw [← A.card_span_unmatched hS, ← A.card_span_unmatched hT]
  exact Finset.card_le_card (Finset.sdiff_subset_sdiff (A.rightSpan_mono h) le_rfl)

theorem leftSpan_sourceBlock_card_le (A : WordMatching x y q) {w : ℕ} (hw : 0 < w) (i : ℕ) :
    (A.symm.rightSpan (A.sourceBlock w i)).card ≤ w := by
  let f : Fin x.length → Fin w := fun j => ⟨j.val % w, Nat.mod_lt _ hw⟩
  have hquot (j : Fin x.length) (hj : j ∈ A.symm.rightSpan (A.sourceBlock w i)) : j.val/w = i := by
    obtain ⟨_, k, hk, l, hl, hkj, hjl⟩ := Finset.mem_filter.mp hj
    have hk := (A.mem_sourceBlock w i k).mp hk
    have hl := (A.mem_sourceBlock w i l).mp hl
    have h1 := Nat.div_le_div_right (c := w) (show (A.left k).val ≤ j.val from hkj)
    have h2 := Nat.div_le_div_right (c := w) (show j.val ≤ (A.left l).val from hjl)
    omega
  have hinj : Set.InjOn f (↑(A.symm.rightSpan (A.sourceBlock w i)) : Set (Fin x.length)) := by
    intro j hj k hk he
    have hj := hquot j hj
    have hk := hquot k hk
    have hf : j.val % w = k.val % w := congrArg Fin.val he
    have h1 := Nat.mod_add_div j.val w
    have h2 := Nat.mod_add_div k.val w
    rw [hj, hf] at h1
    rw [hk] at h2
    apply Fin.ext
    omega
  simpa using Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj

theorem left_span_holes_le_sourceLoss (A : WordMatching x y q) {w : ℕ} (hw : 0 < w)
    {i : ℕ} {S : Finset (Fin q)} (hS : ConvexIndices S) (h : S ⊆ A.sourceBlock w i) :
    (A.symm.rightSpan S).card - S.card ≤ A.sourceLoss w i := by
  exact (A.symm.span_holes_mono hS (A.sourceBlock_convex w i) h).trans
    (Nat.sub_le_sub_right (A.leftSpan_sourceBlock_card_le hw i) _)

theorem right_span_holes_le_spanLoss (A : WordMatching x y q) {w i : ℕ}
    {S : Finset (Fin q)} (hS : ConvexIndices S) (h : S ⊆ A.sourceBlock w i) :
    (A.rightSpan S).card - S.card ≤ A.spanLoss w i :=
  A.span_holes_mono hS (A.sourceBlock_convex w i) h

end WordMatching

end FiniteCircle

end OAI
