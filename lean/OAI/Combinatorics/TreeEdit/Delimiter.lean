import OAI.Combinatorics.TreeEdit.WordOperations

namespace OAI

namespace TreeEdit.Delimiter
open scoped BigOperators
open Classical

lemma eq_of_full_lcs {α : Type*} {x y : List α} (hl : x.length = y.length)
    (hc : x.length ≤ lcs x y) : x = y := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  have hzx : z = x := hx.eq_of_length (by have := hx.length_le; omega)
  have hzy : z = y := hy.eq_of_length (by have := hx.length_le; omega)
  exact hzx.symm.trans hzy

def Synchronizing {α : Type*} {B : ℕ} (c : α → Word Bool B) : Prop :=
  ∀ (x : List α) (a : α) (n : ℕ), n+B ≤ (encode c x).length →
    segment (encode c x) n B = (c a).val →
      ∃ i : Fin x.length, n = i.val*B ∧ x.get i = a

lemma full_fiber {M B N : ℕ} (hB : 0 < B) (f : Fin N ↪o Fin (M*B))
    (a : Fin M) (hc : (Finset.univ.filter (fun i => blockIndex hB (f i) = a)).card = B) :
    ∃ (hs : (Finset.univ.filter (fun i => blockIndex hB (f i) = a)).Nonempty),
      (f ((Finset.univ.filter (fun i => blockIndex hB (f i) = a)).min' hs)).val = a.val*B ∧
      (indexSpan f (Finset.univ.filter (fun i => blockIndex hB (f i) = a))).card = B := by
  let S := Finset.univ.filter (fun i => blockIndex hB (f i) = a)
  have hs : S.Nonempty := Finset.card_pos.mp (by change S.card = B at hc; omega)
  have hl : blockIndex hB (f (S.min' hs)) = a := (Finset.mem_filter.mp (S.min'_mem hs)).2
  have hu : blockIndex hB (f (S.max' hs)) = a := (Finset.mem_filter.mp (S.max'_mem hs)).2
  have hw := span_in_block hB f S hs (hl.trans hu.symm)
  have hge := card_le_indexSpan f S
  have he : (indexSpan f S).card = B := by change S.card = B at hc; omega
  have hm : (f (S.min' hs)).val % B = 0 := by omega
  have hd := Nat.div_add_mod (f (S.min' hs)).val B
  have hq := congrArg Fin.val hl
  change (f (S.min' hs)).val / B = a.val at hq
  refine ⟨hs, ?_, he⟩
  rw [hq, hm, Nat.add_zero, Nat.mul_comm] at hd
  exact hd.symm

lemma good_fiber_matches {α : Type*} {M B N : ℕ} (hB : 0 < B)
    (c : α → Word Bool B) (hc : Synchronizing c) (x y : Word α M)
    (f g : Fin N ↪o Fin (M*B))
    (hfg : ∀ i, (encode c x.val).get (Fin.cast (by rw [length_encode, x.property]) (f i)) =
      (encode c y.val).get (Fin.cast (by rw [length_encode, y.property]) (g i)))
    (a : Fin M) (hfull : (Finset.univ.filter (fun i => blockIndex hB (f i) = a)).card = B)
    (hgap : (indexSpan g (Finset.univ.filter (fun i => blockIndex hB (f i) = a))).card = B) :
    ∃ (hs : (Finset.univ.filter (fun i => blockIndex hB (f i) = a)).Nonempty) (b : Fin M),
      (g ((Finset.univ.filter (fun i => blockIndex hB (f i) = a)).min' hs)).val = b.val*B ∧
      x.val.get (Fin.cast x.property.symm a) = y.val.get (Fin.cast y.property.symm b) := by
  let S := Finset.univ.filter (fun i => blockIndex hB (f i) = a)
  obtain ⟨hs, hstart, hspan⟩ := full_fiber hB f a hfull
  let f' := f.comp (Fin.castOrderIso (by rw [length_encode, x.property] : M*B = (encode c x.val).length)).toOrderEmbedding
  let g' := g.comp (Fin.castOrderIso (by rw [length_encode, y.property] : M*B = (encode c y.val).length)).toOrderEmbedding
  have hbase := span_card_le_lcs (encode c x.val) (encode c y.val) f' g' hfg S hs
  have hfc : (indexSpan f' S).card = B := (indexSpan_card_cast _ f S).trans hspan
  have hgc : (indexSpan g' S).card = B := (indexSpan_card_cast _ g S).trans hgap
  have hxs : segment (encode c x.val) (f' (S.min' hs)).val B = (c (x.val.get (Fin.cast x.property.symm a))).val := by
    change segment (encode c x.val) (f (S.min' hs)).val B = _
    rw [hstart]
    have hh := segment_encode_block c x.val a.val 0 B (by rw [x.property]; exact a.isLt) (by omega)
    simpa only [Nat.add_zero, segment, List.drop_zero, ← (c x.val[a.val]).property, List.take_length, List.get_eq_getElem, Fin.val_cast] using hh
  have hgy : (g' (S.min' hs)).val+B ≤ (encode c y.val).length := by
    simpa only [hgc] using span_bounds g' S hs
  have hfx : (f' (S.min' hs)).val+B ≤ (encode c x.val).length := by
    simpa only [hfc] using span_bounds f' S hs
  have heq : segment (encode c y.val) (g' (S.min' hs)).val B = (c (x.val.get (Fin.cast x.property.symm a))).val := by
    rw [hfc, hgc, hfull] at hbase
    have he := eq_of_full_lcs (x := segment (encode c x.val) (f' (S.min' hs)).val B) (y := segment (encode c y.val) (g' (S.min' hs)).val B) (by rw [length_segment _ hfx, length_segment _ hgy])
      (by simpa only [length_segment _ hfx] using hbase)
    exact he.symm.trans hxs
  obtain ⟨b, hb, hlabel⟩ := hc y.val (x.val.get (Fin.cast x.property.symm a)) _ hgy heq
  exact ⟨hs, Fin.cast y.property b, hb, hlabel.symm⟩

lemma alignment_bound {α : Type*} {M B N : ℕ} (hB : 0 < B)
    (c : α → Word Bool B) (hc : Synchronizing c) (x y : Word α M)
    (f g : Fin N ↪o Fin (M*B))
    (hfg : ∀ i, (encode c x.val).get (Fin.cast (by rw [length_encode, x.property]) (f i)) =
      (encode c y.val).get (Fin.cast (by rw [length_encode, y.property]) (g i))) :
    M ≤ lcs x.val y.val + 2*(M*B-N) := by
  let S (a : Fin M) := Finset.univ.filter (fun i => blockIndex hB (f i) = a)
  let G := Finset.univ.filter (fun a : Fin M => (S a).card = B ∧ (indexSpan g (S a)).card = B)
  have hgood (a : Fin M) (ha : a ∈ G) := good_fiber_matches hB c hc x y f g hfg a
    (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
  let e := G.orderEmbOfFin rfl
  have hem (i : Fin G.card) : e i ∈ G := G.orderEmbOfFin_mem rfl i
  let minPos (i : Fin G.card) := (S (e i)).min' (hgood (e i) (hem i)).choose
  let b (i : Fin G.card) := (hgood (e i) (hem i)).choose_spec.choose
  have hb (i : Fin G.card) : (g (minPos i)).val = (b i).val*B := (hgood (e i) (hem i)).choose_spec.choose_spec.1
  have hl (i : Fin G.card) : x.val.get (Fin.cast x.property.symm (e i)) = y.val.get (Fin.cast y.property.symm (b i)) :=
    (hgood (e i) (hem i)).choose_spec.choose_spec.2
  have hsmin (i : Fin G.card) : blockIndex hB (f (minPos i)) = e i :=
    (Finset.mem_filter.mp ((S (e i)).min'_mem _)).2
  have hminmono : StrictMono minPos := by
    intro i j hij
    by_contra hn
    have h := blockIndex_monotone hB f (le_of_not_gt hn)
    dsimp only at h
    rw [hsmin, hsmin] at h
    exact not_le_of_gt (e.strictMono hij) h
  have hbmono : StrictMono b := by
    intro i j hij
    have hh := g.strictMono (hminmono hij)
    change (g (minPos i)).val < (g (minPos j)).val at hh
    rw [hb, hb] at hh
    exact (Nat.mul_lt_mul_right hB).mp hh
  have hglcs : G.card ≤ lcs x.val y.val := Alignment.le_lcs
    ⟨e.comp (Fin.castOrderIso x.property.symm).toOrderEmbedding,
      (OrderEmbedding.ofStrictMono b hbmono).comp (Fin.castOrderIso y.property.symm).toOrderEmbedding, hl⟩
  have hbad : ∀ a : Fin M, (if a ∈ G then 0 else 1) ≤
      (B-(S a).card) + ((indexSpan g (S a)).card - (S a).card) := by
    intro a
    have hc' := card_block_fiber hB f a
    have hs' := card_le_indexSpan g (S a)
    split_ifs with ha
    · omega
    · have hn : ¬ ((S a).card = B ∧ (indexSpan g (S a)).card = B) := by simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and] using ha
      change (S a).card ≤ B at hc'
      omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hbad a)
  have hloss := sum_block_losses hB f
  have hgap := sum_span_gaps_le g (fun i => blockIndex hB (f i)) (blockIndex_monotone hB f)
  have hcount : (∑ a : Fin M, if a ∈ G then 0 else 1) = M-G.card := by
    simpa only [ite_not, Finset.sum_boole, Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_sdiff_of_subset (Finset.subset_univ G), Finset.card_univ, Fintype.card_fin, Nat.cast_id] using
      (Finset.sum_boole (fun a : Fin M => a ∉ G) Finset.univ : (∑ a : Fin M, if a ∉ G then (1 : ℕ) else 0) = _)
  rw [hcount, Finset.sum_add_distrib] at hsum
  change (∑ a : Fin M, (B-(S a).card)) = M*B-N at hloss
  change (∑ a : Fin M, ((indexSpan g (S a)).card-(S a).card)) ≤ M*B-N at hgap
  rw [hloss] at hsum
  have hcard : G.card ≤ M := by simpa using Finset.card_le_univ G
  omega

end TreeEdit.Delimiter

namespace TreeEdit.Delimiter
open scoped BigOperators
open Classical

lemma deficit_bound {α : Type*} {M B : ℕ} (hB : 0 < B) (c : α → Word Bool B)
    (hc : Synchronizing c) (x y : Word α M) :
    deficit x.val y.val ≤ 2*deficit (encode c x.val) (encode c y.val) := by
  obtain ⟨A⟩ := exists_lcs_alignment (encode c x.val) (encode c y.val)
  have hx : (encode c x.val).length = M*B := by rw [length_encode, x.property]
  have hy : (encode c y.val).length = M*B := by rw [length_encode, y.property]
  let f := A.left.comp (Fin.castOrderIso hx).toOrderEmbedding
  let g := A.right.comp (Fin.castOrderIso hy).toOrderEmbedding
  have hfg : ∀ i, (encode c x.val).get (Fin.cast hx.symm (f i)) =
      (encode c y.val).get (Fin.cast hy.symm (g i)) := A.agree
  have hh := alignment_bound hB c hc x y f g hfg
  dsimp only [deficit]
  rw [hx, x.property]
  omega

def bit {t : ℕ} (label : Fin t → Bool) (i : Fin (2*t+3)) : Bool :=
  if hi : i.val < 2 then true else
    if h : i.val % 2 = 1 then label ⟨(i.val-3)/2, by have := i.isLt; omega⟩ else false

def code {α : Type*} {t : ℕ} (label : α → (Fin t → Bool)) (a : α) : Word Bool (2*t+3) :=
  vectorWord (bit (label a))

lemma bit_true {t : ℕ} (label : Fin t → Bool) (i : Fin (2*t+3)) (h : bit label i = true) :
    i.val = 0 ∨ i.val % 2 = 1 := by
  unfold bit at h
  split_ifs at h with hi hi
  · omega
  · exact Or.inr hi

lemma bit_label {t : ℕ} (label : Fin t → Bool) (i : Fin t) :
    bit label ⟨3+2*i.val, by have := i.isLt; omega⟩ = label i := by
  have he : (3+2*i.val) % 2 = 1 := by omega
  simp only [bit, show ¬ 3+2*i.val < 2 by omega, dite_false, he, dite_true]
  congr 1
  apply Fin.ext
  change (3+2*i.val-3)/2 = i.val
  omega

lemma code_injective {α : Type*} {t : ℕ} (label : α → (Fin t → Bool)) (hl : Function.Injective label) :
    Function.Injective (code label) := by
  intro a b hab
  apply hl
  funext i
  have h := congrArg (fun w : Word Bool (2*t+3) =>
    w.val.get (Fin.cast w.property.symm ⟨3+2*i.val, by have := i.isLt; omega⟩)) hab
  simp only [code, vectorWord, List.get_eq_getElem, List.getElem_ofFn] at h
  change bit (label a) ⟨3+2*i.val, _⟩ = bit (label b) ⟨3+2*i.val, _⟩ at h
  simpa only [bit_label] using h

lemma get_position {α : Type*} {B : ℕ} (hB : 0 < B) (c : α → Word Bool B) (x : List α)
    (p : ℕ) (hp : p < (encode c x).length) :
    (encode c x)[p] = (c (x[p/B]'((Nat.div_lt_iff_lt_mul hB).mpr (by rwa [length_encode] at hp)))).val[p%B]'(by
      rw [(c _).property]; exact Nat.mod_lt _ hB) := by
  have hh := get_encode_block c x (p/B) (p%B) ((Nat.div_lt_iff_lt_mul hB).mpr (by rwa [length_encode] at hp)) (Nat.mod_lt p hB)
  simpa only [Nat.mul_comm (p/B) B, Nat.div_add_mod] using hh

lemma bit_position {α : Type*} {t : ℕ} (label : α → (Fin t → Bool)) (x : List α)
    (p : ℕ) (hp : p < (encode (code label) x).length) :
    (encode (code label) x)[p] = bit (label (x[p/(2*t+3)]'((Nat.div_lt_iff_lt_mul (by omega : 0 < 2*t+3)).mpr (by rwa [length_encode] at hp))))
      ⟨p%(2*t+3), Nat.mod_lt _ (by omega)⟩ := by
  rw [get_position (by omega)]
  simp only [code, vectorWord, List.getElem_ofFn]

lemma marker {α : Type*} {t : ℕ} (label : α → (Fin t → Bool)) (x : List α)
    (p : ℕ) (hp : p+1 < (encode (code label) x).length)
    (h0 : (encode (code label) x)[p]'(by omega) = true)
    (h1 : (encode (code label) x)[p+1] = true) : p%(2*t+3) = 0 := by
  rw [bit_position] at h0 h1
  have h0' := bit_true _ _ h0
  have h1' := bit_true _ _ h1
  change p%(2*t+3) = 0 ∨ p%(2*t+3)%2 = 1 at h0'
  change (p+1)%(2*t+3) = 0 ∨ (p+1)%(2*t+3)%2 = 1 at h1'
  have hr := Nat.mod_lt p (by omega : 0 < 2*t+3)
  have hr' := Nat.mod_lt (p+1) (by omega : 0 < 2*t+3)
  by_contra hn
  have ho : p%(2*t+3)%2 = 1 := h0'.resolve_left hn
  have hend : p%(2*t+3)+1 < 2*t+3 := by omega
  have he : (p+1)%(2*t+3) = p%(2*t+3)+1 := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < 2*t+3), Nat.mod_eq_of_lt hend]
  rw [he] at h1'
  omega

lemma code_synchronizing {α : Type*} {t : ℕ} (label : α → (Fin t → Bool)) (hl : Function.Injective label) :
    Synchronizing (code label) := by
  intro x a n hn he
  have h0 : (encode (code label) x)[n]'(by omega) = true := by
    have hh := congrArg (fun l : List Bool => l[0]?) he
    have hbit : (code label a).val[0]'(by rw [(code label a).property]; omega) = true := by simp only [code, vectorWord, List.getElem_ofFn, bit]; norm_num
    rw [List.getElem?_eq_getElem (by rw [length_segment _ hn]; omega),
      List.getElem?_eq_getElem (by rw [(code label a).property]; omega)] at hh
    simpa only [Option.some.injEq, segment_get, Nat.add_zero, hbit] using hh
  have h1 : (encode (code label) x)[n+1]'(by omega) = true := by
    have hh := congrArg (fun l : List Bool => l[1]?) he
    have hbit : (code label a).val[1]'(by rw [(code label a).property]; omega) = true := by simp only [code, vectorWord, List.getElem_ofFn, bit]; norm_num
    rw [List.getElem?_eq_getElem (by rw [length_segment _ hn]; omega),
      List.getElem?_eq_getElem (by rw [(code label a).property]; omega)] at hh
    simpa only [Option.some.injEq, segment_get, hbit] using hh
  have hm := marker label x n (by omega) h0 h1
  have hbi : n/(2*t+3) < x.length := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [← length_encode (code label) x]; omega)
  let b : Fin x.length := ⟨n/(2*t+3), hbi⟩
  have hstart : n = b.val*(2*t+3) := by
    have hd := Nat.div_add_mod n (2*t+3)
    rw [hm, Nat.add_zero, Nat.mul_comm] at hd
    exact hd.symm
  refine ⟨b, hstart, ?_⟩
  apply code_injective label hl
  apply Subtype.ext
  have hh := segment_encode_block (code label) x b.val 0 (2*t+3) b.isLt (by omega)
  have hs : segment (encode (code label) x) n (2*t+3) = (code label (x.get b)).val := by
    rw [hstart]
    simpa only [Nat.add_zero, segment, List.drop_zero, ← (code label x[b.val]).property, List.take_length, List.get_eq_getElem] using hh
  exact hs.symm.trans he

def width (A : ℕ) : ℕ := 2*Nat.clog 2 A+3

lemma width_eq (A : ℕ) : width A = 2*⌈Real.log (A : ℝ)/Real.log 2⌉₊+3 := by
  rw [width, ← Real.natCeil_logb_natCast 2 A]
  rfl

lemma exists_code (α : Type*) [Fintype α] :
    ∃ c : α → Word Bool (width (Fintype.card α)), Synchronizing c := by
  have hcard : Fintype.card α ≤ Fintype.card (Fin (Nat.clog 2 (Fintype.card α)) → Bool) := by
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using Nat.le_pow_clog (by norm_num : 1 < 2) (Fintype.card α)
  let label := (Fintype.equivFin α).toEmbedding.trans ((Fin.castLEEmb hcard).trans (Fintype.equivFin (Fin (Nat.clog 2 (Fintype.card α)) → Bool)).symm.toEmbedding)
  exact ⟨code label, code_synchronizing label label.injective⟩

theorem transfer (α : Type*) [Fintype α] :
    ∃ c : α → Word Bool (width (Fintype.card α)), ∀ (n : ℕ) (x y : Word α n),
      deficit x.val y.val ≤ 2*deficit (encode c x.val) (encode c y.val) ∧
      (deficit x.val y.val : ℝ)/2 ≤ ed (encode c x.val) (encode c y.val) ∧
      ed (encode c x.val) (encode c y.val) ≤ width (Fintype.card α)*ed x.val y.val := by
  obtain ⟨c, hc⟩ := exists_code α
  refine ⟨c, fun n x y => ?_⟩
  have hh := deficit_bound (by dsimp [width]; omega) c hc x y
  refine ⟨hh, ?_, ed_encode_le c x.val y.val⟩
  have he := deficit_le_ed (encode c x.val) (encode c y.val)
  have hhr : (deficit x.val y.val : ℝ) ≤ 2*deficit (encode c x.val) (encode c y.val) := by exact_mod_cast hh
  have her : (deficit (encode c x.val) (encode c y.val) : ℝ) ≤ ed (encode c x.val) (encode c y.val) := by exact_mod_cast he
  linarith

end TreeEdit.Delimiter

end OAI
