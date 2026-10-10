import OAI.Combinatorics.BinaryEdit.MatchingSublist

namespace OAI

namespace TreeEdit.BinaryLower

/-- Shift an index known to lie in a segment into that segment's index type. -/
def segmentIndex {α : Type*} (x : List α) (start width : ℕ)
    (i : Fin x.length) (hlo : start ≤ (i : ℕ)) (hhi : (i : ℕ) < start + width) :
    Fin ((x.drop start).take width).length :=
  ⟨(i : ℕ) - start, by
    simp only [List.length_take, List.length_drop]
    apply lt_min
    · omega
    · omega⟩

/-- Shifting indices into a list segment preserves the selected letter. -/
theorem get_segmentIndex {α : Type*} (x : List α) (start width : ℕ)
    (i : Fin x.length) (hlo : start ≤ (i : ℕ)) (hhi : (i : ℕ) < start + width) :
    ((x.drop start).take width).get (segmentIndex x start width i hlo hhi) =
      x.get i := by
  simp only [List.get_eq_getElem, segmentIndex, List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- An increasing matching confined to two intervals is a common subsequence
of the corresponding contiguous segments. -/
theorem matching_in_segments_le_lcs {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t))
    (a b p q : ℕ)
    (hi_lo : ∀ t, a ≤ (i t : ℕ)) (hi_hi : ∀ t, (i t : ℕ) < a + p)
    (hj_lo : ∀ t, b ≤ (j t : ℕ)) (hj_hi : ∀ t, (j t : ℕ) < b + q) :
    k ≤ lcs ((x.drop a).take p) ((y.drop b).take q) := by
  let u : Fin k → Fin ((x.drop a).take p).length := fun t =>
    segmentIndex x a p (i t) (hi_lo t) (hi_hi t)
  let v : Fin k → Fin ((y.drop b).take q).length := fun t =>
    segmentIndex y b q (j t) (hj_lo t) (hj_hi t)
  apply matching_length_le_lcs _ _ u v
  · intro s t hst
    have h := hi hst
    have hs := hi_lo s
    have ht := hi_lo t
    change (i s : ℕ) - a < (i t : ℕ) - a
    omega
  · intro s t hst
    have h := hj hst
    have hs := hj_lo s
    have ht := hj_lo t
    change (j s : ℕ) - b < (j t : ℕ) - b
    omega
  · intro t
    exact (get_segmentIndex x a p (i t) (hi_lo t) (hi_hi t)).trans
      ((hlabel t).trans (get_segmentIndex y b q (j t) (hj_lo t) (hj_hi t)).symm)

/-- Restricting a matching to any finite collection of edges lying in two
segments gives the same bound for the cardinality of that collection. -/
theorem matching_subset_in_segments_le_lcs {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t))
    (S : Finset (Fin k)) (a b p q : ℕ)
    (hi_lo : ∀ t ∈ S, a ≤ (i t : ℕ)) (hi_hi : ∀ t ∈ S, (i t : ℕ) < a + p)
    (hj_lo : ∀ t ∈ S, b ≤ (j t : ℕ)) (hj_hi : ∀ t ∈ S, (j t : ℕ) < b + q) :
    S.card ≤ lcs ((x.drop a).take p) ((y.drop b).take q) := by
  let e : Fin S.card ↪o Fin k := S.orderEmbOfFin rfl
  have he (t : Fin S.card) : e t ∈ S := S.orderEmbOfFin_mem rfl t
  apply matching_in_segments_le_lcs x y (i ∘ e) (j ∘ e)
    (hi.comp e.strictMono) (hj.comp e.strictMono) (fun t => hlabel (e t)) a b p q
  · exact fun t => hi_lo (e t) (he t)
  · exact fun t => hi_hi (e t) (he t)
  · exact fun t => hj_lo (e t) (he t)
  · exact fun t => hj_hi (e t) (he t)

/-- Natural-index interface for span-counting arguments. -/
theorem matching_subset_in_segments_le_lcs_nat {α : Type*} (x y : List α) {k : ℕ}
    (i j : Fin k → ℕ) (hi : StrictMono i) (hj : StrictMono j)
    (hix : ∀ t, i t < x.length) (hjy : ∀ t, j t < y.length)
    (hlabel : ∀ t, x.get ⟨i t, hix t⟩ = y.get ⟨j t, hjy t⟩)
    (S : Finset (Fin k)) (a b p q : ℕ)
    (hi_lo : ∀ t ∈ S, a ≤ i t) (hi_hi : ∀ t ∈ S, i t < a + p)
    (hj_lo : ∀ t ∈ S, b ≤ j t) (hj_hi : ∀ t ∈ S, j t < b + q) :
    S.card ≤ lcs ((x.drop a).take p) ((y.drop b).take q) := by
  exact matching_subset_in_segments_le_lcs x y
    (fun t => ⟨i t, hix t⟩) (fun t => ⟨j t, hjy t⟩)
    hi hj hlabel S a b p q hi_lo hi_hi hj_lo hj_hi

/-- An increasing matching confined to two intervals is a common subsequence
of the corresponding contiguous segments. -/
theorem common_sublist_in_segments {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t))
    (a b p q : ℕ)
    (hi_lo : ∀ t, a ≤ (i t : ℕ)) (hi_hi : ∀ t, (i t : ℕ) < a + p)
    (hj_lo : ∀ t, b ≤ (j t : ℕ)) (hj_hi : ∀ t, (j t : ℕ) < b + q) :
    ∃ z : List α, z.Sublist ((x.drop a).take p) ∧
      z.Sublist ((y.drop b).take q) ∧ z.length = k := by
  let u : Fin k → Fin ((x.drop a).take p).length := fun t =>
    segmentIndex x a p (i t) (hi_lo t) (hi_hi t)
  let v : Fin k → Fin ((y.drop b).take q).length := fun t =>
    segmentIndex y b q (j t) (hj_lo t) (hj_hi t)
  apply common_sublist_of_strict_matching _ _ u v
  · intro s t hst
    have h := hi hst
    have hs := hi_lo s
    have ht := hi_lo t
    change (i s : ℕ) - a < (i t : ℕ) - a
    omega
  · intro s t hst
    have h := hj hst
    have hs := hj_lo s
    have ht := hj_lo t
    change (j s : ℕ) - b < (j t : ℕ) - b
    omega
  · intro t
    exact (get_segmentIndex x a p (i t) (hi_lo t) (hi_hi t)).trans
      ((hlabel t).trans (get_segmentIndex y b q (j t) (hj_lo t) (hj_hi t)).symm)

/-- Witness form of the restricted matching-to-segment bound. -/
theorem common_sublist_subset_in_segments {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t))
    (S : Finset (Fin k)) (a b p q : ℕ)
    (hi_lo : ∀ t ∈ S, a ≤ (i t : ℕ)) (hi_hi : ∀ t ∈ S, (i t : ℕ) < a + p)
    (hj_lo : ∀ t ∈ S, b ≤ (j t : ℕ)) (hj_hi : ∀ t ∈ S, (j t : ℕ) < b + q) :
    ∃ z : List α, z.Sublist ((x.drop a).take p) ∧
      z.Sublist ((y.drop b).take q) ∧ z.length = S.card := by
  let e : Fin S.card ↪o Fin k := S.orderEmbOfFin rfl
  have he (t : Fin S.card) : e t ∈ S := S.orderEmbOfFin_mem rfl t
  apply common_sublist_in_segments x y (i ∘ e) (j ∘ e)
    (hi.comp e.strictMono) (hj.comp e.strictMono) (fun t => hlabel (e t)) a b p q
  · exact fun t => hi_lo (e t) (he t)
  · exact fun t => hi_hi (e t) (he t)
  · exact fun t => hj_lo (e t) (he t)
  · exact fun t => hj_hi (e t) (he t)

/-- Raw fixed-length function interface for the segment witness. -/
theorem common_sublist_subset_ofFn_segments {α : Type*} {n m k : ℕ}
    (x : Fin n → α) (y : Fin m → α)
    (i : Fin k → Fin n) (j : Fin k → Fin m)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x (i t) = y (j t))
    (S : Finset (Fin k)) (a b p q : ℕ)
    (hi_lo : ∀ t ∈ S, a ≤ (i t : ℕ)) (hi_hi : ∀ t ∈ S, (i t : ℕ) < a + p)
    (hj_lo : ∀ t ∈ S, b ≤ (j t : ℕ)) (hj_hi : ∀ t ∈ S, (j t : ℕ) < b + q) :
    ∃ z : List α, z.Sublist (((List.ofFn x).drop a).take p) ∧
      z.Sublist (((List.ofFn y).drop b).take q) ∧ z.length = S.card := by
  let f : Fin k → Fin (List.ofFn x).length :=
    fun t => Fin.cast List.length_ofFn.symm (i t)
  let g : Fin k → Fin (List.ofFn y).length :=
    fun t => Fin.cast List.length_ofFn.symm (j t)
  have hf : StrictMono f := (Fin.cast_strictMono _).comp hi
  have hg : StrictMono g := (Fin.cast_strictMono _).comp hj
  have hmatch : ∀ t, (List.ofFn x).get (f t) = (List.ofFn y).get (g t) := by
    intro t
    simpa [f, g] using hlabel t
  exact common_sublist_subset_in_segments (List.ofFn x) (List.ofFn y)
    f g hf hg hmatch S a b p q hi_lo hi_hi hj_lo hj_hi

end TreeEdit.BinaryLower

end OAI
