import OAI.Combinatorics.TreeEdit.Alignments

namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

def segment {β : Type*} (x : List β) (start len : ℕ) : List β :=
  (x.drop start).take len

theorem length_segment {β : Type*} (x : List β) {start len : ℕ}
    (h : start + len ≤ x.length) : (segment x start len).length = len := by
  simp only [segment, List.length_take, List.length_drop]
  omega

theorem segment_get {β : Type*} (x : List β) (start len i : ℕ)
    (hi : i < (segment x start len).length) :
    (segment x start len)[i] = x[start + i]'(by
      simp only [segment, List.length_take, List.length_drop] at hi
      omega) := by
  simp only [segment, List.getElem_take, List.getElem_drop]

theorem take_segment {β : Type*} (x : List β) (start len a : ℕ) (ha : a ≤ len) :
    (segment x start len).take a = segment x start a := by
  simp [segment, List.take_take, Nat.min_eq_left ha]

theorem lcs_le_take_left (x y : List α) (a : ℕ) :
    lcs x y ≤ lcs (x.take a) y + (x.length - a) := by
  have h := lcs_script_loss y (sublist_script (List.take_sublist a x))
  rw [lcs_comm y x, lcs_comm y (x.take a)] at h
  simp only [List.length_take] at h
  have he : x.length - min a x.length = x.length - a := by omega
  rwa [he] at h

theorem lcs_le_take_both (x y : List α) (a : ℕ) :
    lcs x y ≤ lcs (x.take a) (y.take a) + (x.length - a) + (y.length - a) := by
  have hl := lcs_le_take_left x y a
  have hr := lcs_le_take_left y (x.take a) a
  rw [lcs_comm y (x.take a), lcs_comm (y.take a) (x.take a)] at hr
  omega

theorem get_encode_block {P : ℕ} (c : α → Word Bool P) (x : List α)
    (i r : ℕ) (hi : i < x.length) (hr : r < P) :
    (encode c x)[i * P + r]'(by
      rw [length_encode]
      have hh := Nat.mul_le_mul_right P (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at hh
      omega) = (c x[i]).val[r]'(by rw [(c x[i]).property]; exact hr) := by
  induction x generalizing i with
  | nil => simp at hi
  | cons a x ih =>
      simp only [encode_cons]
      cases i with
      | zero =>
          simpa using List.getElem_append_left (as := (c a).val) (bs := encode c x)
            (i := r) (by rw [(c a).property]; exact hr)
      | succ i =>
          rw [List.getElem_append_right (by rw [(c a).property, Nat.add_mul]; omega)]
          have he : (i + 1) * P + r - (c a).val.length = i * P + r := by
            rw [(c a).property, Nat.add_mul]; omega
          simpa only [he, List.getElem_cons_succ] using ih i (by simpa using hi)

theorem segment_encode_block {P : ℕ} (c : α → Word Bool P) (x : List α)
    (i start len : ℕ) (hi : i < x.length) (hseg : start + len ≤ P) :
    segment (encode c x) (i * P + start) len = segment (c x[i]).val start len := by
  have hb : i * P + start + len ≤ (encode c x).length := by
    rw [length_encode]
    have hh := Nat.mul_le_mul_right P (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at hh
    omega
  have hc : start + len ≤ (c x[i]).val.length := by rwa [(c x[i]).property]
  apply List.ext_getElem
  · rw [length_segment _ hb, length_segment _ hc]
  · intro j hj hj'
    rw [segment_get, segment_get]
    have hjl : j < len := by rwa [length_segment _ hb] at hj
    simpa only [Nat.add_assoc] using get_encode_block c x i (start + j) hi (by omega)

theorem span_bounds {N L : ℕ} (f : Fin N ↪o Fin L) (s : Finset (Fin N))
    (hs : s.Nonempty) :
    (f (s.min' hs)).val + (indexSpan f s).card ≤ L := by
  rw [indexSpan, dite_eq_left hs, Fin.card_Icc]
  have hle := f.monotone (s.min'_le_max' hs)
  have hlt := (f (s.max' hs)).isLt
  omega

theorem span_length_formula {N L : ℕ} (f : Fin N ↪o Fin L) (s : Finset (Fin N))
    (hs : s.Nonempty) :
    (f (s.min' hs)).val + (indexSpan f s).card = (f (s.max' hs)).val + 1 := by
  rw [indexSpan, dite_eq_left hs, Fin.card_Icc]
  have hle := f.monotone (s.min'_le_max' hs)
  omega

theorem span_card_le_lcs {β : Type*} {N : ℕ} (x y : List β)
    (f : Fin N ↪o Fin x.length) (g : Fin N ↪o Fin y.length)
    (hfg : ∀ i, x.get (f i) = y.get (g i))
    (s : Finset (Fin N)) (hs : s.Nonempty) :
    s.card ≤ lcs (segment x (f (s.min' hs)).val (indexSpan f s).card)
      (segment y (g (s.min' hs)).val (indexSpan g s).card) := by
  let e := s.orderEmbOfFin rfl
  let a := (f (s.min' hs)).val
  let b := (g (s.min' hs)).val
  let X := segment x a (indexSpan f s).card
  let Y := segment y b (indexSpan g s).card
  have hX : X.length = (indexSpan f s).card := length_segment _ (span_bounds f s hs)
  have hY : Y.length = (indexSpan g s).card := length_segment _ (span_bounds g s hs)
  have hlo (i : Fin s.card) : a ≤ (f (e i)).val :=
    f.monotone (s.min'_le _ (s.orderEmbOfFin_mem rfl i))
  have hro (i : Fin s.card) : b ≤ (g (e i)).val :=
    g.monotone (s.min'_le _ (s.orderEmbOfFin_mem rfl i))
  have hli (i : Fin s.card) : (f (e i)).val - a < X.length := by
    rw [hX]
    have hu := f.monotone (s.le_max' _ (s.orderEmbOfFin_mem rfl i))
    have hf := span_length_formula f s hs
    have hl := hlo i
    dsimp [a, e] at *
    omega
  have hri (i : Fin s.card) : (g (e i)).val - b < Y.length := by
    rw [hY]
    have hu := g.monotone (s.le_max' _ (s.orderEmbOfFin_mem rfl i))
    have hf := span_length_formula g s hs
    have hl := hro i
    dsimp [b, e] at *
    omega
  let fl : Fin s.card → Fin X.length := fun i => ⟨(f (e i)).val - a, hli i⟩
  let gr : Fin s.card → Fin Y.length := fun i => ⟨(g (e i)).val - b, hri i⟩
  have hfl : StrictMono fl := by
    intro i j hij
    have hi := hlo i
    have hj := hlo j
    have hh := f.strictMono (e.strictMono hij)
    change (f (e i)).val - a < (f (e j)).val - a
    omega
  have hgr : StrictMono gr := by
    intro i j hij
    have hi := hro i
    have hj := hro j
    have hh := g.strictMono (e.strictMono hij)
    change (g (e i)).val - b < (g (e j)).val - b
    omega
  apply Alignment.le_lcs (x := X) (y := Y)
    ⟨OrderEmbedding.ofStrictMono fl hfl, OrderEmbedding.ofStrictMono gr hgr, ?_⟩
  intro i
  change X.get (fl i) = Y.get (gr i)
  simp only [List.get_eq_getElem, X, Y, fl, gr]
  rw [segment_get, segment_get]
  simpa only [Nat.add_sub_of_le (hlo i), Nat.add_sub_of_le (hro i),
    List.get_eq_getElem] using hfg (e i)

def SegmentCode {P : ℕ} (c : α → Word Bool P) (a₀ : ℕ) : Prop :=
  ∀ a b : α, a ≠ b → ∀ start stop len : ℕ, a₀ ≤ len →
    start + len ≤ P → stop + len ≤ P →
    100 * lcs (segment (c a).val start len) (segment (c b).val stop len) ≤ 99 * len

theorem indexSpan_card_cast {N L L' : ℕ} (h : L = L')
    (f : Fin N ↪o Fin L) (s : Finset (Fin N)) :
    (indexSpan (f.comp (Fin.castOrderIso h).toOrderEmbedding) s).card =
      (indexSpan f s).card := by
  subst L'
  rfl

theorem span_in_block {M P N : ℕ} (hP : 0 < P)
    (f : Fin N ↪o Fin (M * P)) (s : Finset (Fin N)) (hs : s.Nonempty)
    (hb : blockIndex hP (f (s.min' hs)) = blockIndex hP (f (s.max' hs))) :
    (f (s.min' hs)).val % P + (indexSpan f s).card ≤ P := by
  have he := congrArg Fin.val hb
  change (f (s.min' hs)).val / P = (f (s.max' hs)).val / P at he
  have hl := span_length_formula f s hs
  have hmin := Nat.mod_add_div (f (s.min' hs)).val P
  have hmax := Nat.mod_add_div (f (s.max' hs)).val P
  have hmod := Nat.mod_lt (f (s.max' hs)).val hP
  rw [he] at hmin
  omega

theorem span_encode_eq {M P N : ℕ} (hP : 0 < P) (c : α → Word Bool P)
    (x : Word α M) (f : Fin N ↪o Fin (M * P))
    (s : Finset (Fin N)) (hs : s.Nonempty)
    (hb : blockIndex hP (f (s.min' hs)) = blockIndex hP (f (s.max' hs))) :
    segment (encode c x.val) (f (s.min' hs)).val (indexSpan f s).card =
      segment (c (x.val.get (Fin.cast x.property.symm
        (blockIndex hP (f (s.min' hs)))))).val
          ((f (s.min' hs)).val % P) (indexSpan f s).card := by
  have hr := span_in_block hP f s hs hb
  have hh := segment_encode_block c x.val
    ((f (s.min' hs)).val / P) ((f (s.min' hs)).val % P)
      (indexSpan f s).card (by
        rw [x.property]
        exact (blockIndex hP (f (s.min' hs))).isLt) hr
  simpa only [Nat.mul_comm ((f (s.min' hs)).val / P) P, Nat.div_add_mod,
    List.get_eq_getElem, blockIndex, Fin.cast_mk] using hh

theorem unequal_pair_bound {M P N a₀ : ℕ} (hP : 0 < P)
    (c : α → Word Bool P) (hc : SegmentCode c a₀) (x y : Word α M)
    (f g : Fin N ↪o Fin (M * P))
    (hfg : ∀ i,
      (encode c x.val).get (Fin.cast (by rw [length_encode, x.property]) (f i)) =
      (encode c y.val).get (Fin.cast (by rw [length_encode, y.property]) (g i)))
    (s : Finset (Fin N)) (hs : s.Nonempty)
    (hf : blockIndex hP (f (s.min' hs)) = blockIndex hP (f (s.max' hs)))
    (hg : blockIndex hP (g (s.min' hs)) = blockIndex hP (g (s.max' hs)))
    (hne : x.val.get (Fin.cast x.property.symm (blockIndex hP (f (s.min' hs)))) ≠
      y.val.get (Fin.cast y.property.symm (blockIndex hP (g (s.min' hs))))) :
    s.card ≤ 100 * ((indexSpan f s).card - s.card +
      ((indexSpan g s).card - s.card)) + a₀ := by
  by_cases ha : a₀ ≤ s.card
  · let f' := f.comp (Fin.castOrderIso (by rw [length_encode, x.property] :
        M * P = (encode c x.val).length)).toOrderEmbedding
    let g' := g.comp (Fin.castOrderIso (by rw [length_encode, y.property] :
        M * P = (encode c y.val).length)).toOrderEmbedding
    have hbase := span_card_le_lcs (encode c x.val) (encode c y.val) f' g' hfg s hs
    have hfc : (indexSpan f' s).card = (indexSpan f s).card := indexSpan_card_cast _ f s
    have hgc : (indexSpan g' s).card = (indexSpan g s).card := indexSpan_card_cast _ g s
    rw [hfc, hgc] at hbase
    change s.card ≤ lcs
      (segment (encode c x.val) (f (s.min' hs)).val (indexSpan f s).card)
      (segment (encode c y.val) (g (s.min' hs)).val (indexSpan g s).card) at hbase
    rw [span_encode_eq hP c x f s hs hf, span_encode_eq hP c y g s hs hg] at hbase
    have hl := card_le_indexSpan f s
    have hr := card_le_indexSpan g s
    have hfb := span_in_block hP f s hs hf
    have hgb := span_in_block hP g s hs hg
    have htrim := lcs_le_take_both
      (segment (c (x.val.get (Fin.cast x.property.symm
        (blockIndex hP (f (s.min' hs)))))).val
          ((f (s.min' hs)).val % P) (indexSpan f s).card)
      (segment (c (y.val.get (Fin.cast y.property.symm
        (blockIndex hP (g (s.min' hs)))))).val
          ((g (s.min' hs)).val % P) (indexSpan g s).card) s.card
    rw [take_segment _ _ _ _ hl, take_segment _ _ _ _ hr] at htrim
    rw [length_segment _ (by rw [(c _).property]; exact hfb),
      length_segment _ (by rw [(c _).property]; exact hgb)] at htrim
    have hc' := hc _ _ hne ((f (s.min' hs)).val % P)
      ((g (s.min' hs)).val % P) s.card ha (by omega) (by omega)
    omega
  · omega

theorem code_alignment_additive {M P N a₀ : ℕ} (hP : 0 < P)
    (c : α → Word Bool P) (hc : SegmentCode c a₀) (x y : Word α M)
    (f g : Fin N ↪o Fin (M * P))
    (hfg : ∀ i,
      (encode c x.val).get (Fin.cast (by rw [length_encode, x.property]) (f i)) =
      (encode c y.val).get (Fin.cast (by rw [length_encode, y.property]) (g i))) :
    P * deficit x.val y.val ≤ 201 * (M * P - N) + 2 * M * a₀ := by
  classical
  let E : Fin N → Prop := fun i =>
    x.val.get (Fin.cast x.property.symm (blockIndex hP (f i))) =
      y.val.get (Fin.cast y.property.symm (blockIndex hP (g i)))
  let good := Finset.univ.filter E
  let bad := Finset.univ.filter (fun i => ¬ E i)
  let key := blockPairKey hP f g
  let fiber := fun k => Finset.univ.filter (fun i => key i = k)
  let gap := fun k => (indexSpan f (fiber k)).card - (fiber k).card +
    ((indexSpan g (fiber k)).card - (fiber k).card)
  have hsame {i j : Fin N} (h : key i = key j) : E i ↔ E j := by
    obtain ⟨hf, hg⟩ := (blockPairKey_eq_iff hP f g i j).mp h
    simp only [E, hf, hg]
  have hgood : good.card ≤ P * lcs x.val y.val := by
    let e := good.orderEmbOfFin rfl
    apply equal_label_alignment_bound hP x y (e.comp f) (e.comp g)
    intro i
    exact (Finset.mem_filter.mp (good.orderEmbOfFin_mem rfl i)).2
  have hone (k : Fin (2 * M)) :
      (bad.filter (fun i => key i = k)).card ≤ 100 * gap k + a₀ := by
    by_cases hb : (bad.filter (fun i => key i = k)).Nonempty
    · obtain ⟨i, hi⟩ := hb
      obtain ⟨hib, hik⟩ := Finset.mem_filter.mp hi
      have hine : ¬ E i := (Finset.mem_filter.mp hib).2
      have hsi : i ∈ fiber k := by simp only [fiber, Finset.mem_filter,
        Finset.mem_univ, true_and]; exact hik
      have hs : (fiber k).Nonempty := ⟨i, hsi⟩
      have hmin : key ((fiber k).min' hs) = k :=
        (Finset.mem_filter.mp ((fiber k).min'_mem hs)).2
      have hmax : key ((fiber k).max' hs) = k :=
        (Finset.mem_filter.mp ((fiber k).max'_mem hs)).2
      obtain ⟨hf, hg⟩ := (blockPairKey_eq_iff hP f g _ _).mp (hmin.trans hmax.symm)
      have hne : ¬ E ((fiber k).min' hs) := fun h =>
        hine ((hsame (hmin.trans hik.symm)).mp h)
      have hbound := unequal_pair_bound hP c hc x y f g hfg (fiber k) hs hf hg hne
      have hsub : bad.filter (fun i => key i = k) ⊆ fiber k := by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩
      exact (Finset.card_le_card hsub).trans hbound
    · rw [Finset.not_nonempty_iff_eq_empty.mp hb]
      simp
  have hbad : bad.card ≤ 200 * (M * P - N) + 2 * M * a₀ := by
    have he := Finset.card_eq_sum_card_fiberwise
      (s := bad) (t := Finset.univ) (f := key) (by simp)
    rw [he]
    calc
      _ ≤ ∑ k : Fin (2 * M), (100 * gap k + a₀) :=
        Finset.sum_le_sum (fun k _ => hone k)
      _ = 100 * (∑ k : Fin (2 * M), gap k) + 2 * M * a₀ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
      _ ≤ 200 * (M * P - N) + 2 * M * a₀ := by
        have hg : (∑ k : Fin (2 * M), gap k) ≤ 2 * (M * P - N) :=
          block_span_gap_budget hP f g
        omega
  have hsplit : good.card + bad.card = N := by
    simpa only [good, bad, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) E
  have hN : N ≤ M * P := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ f.injective
  have hsum : P * deficit x.val y.val + P * lcs x.val y.val = M * P := by
    rw [← Nat.mul_add, deficit, Nat.sub_add_cancel (lcs_le_length_left _ _), x.property]
    exact Nat.mul_comm _ _
  omega

theorem code_deficit_comparison {M P a₀ : ℕ} (hP : 0 < P)
    (hthreshold : 4 * M * a₀ ≤ P) (c : α → Word Bool P)
    (hc : SegmentCode c a₀) (x y : Word α M) :
    P * deficit x.val y.val ≤ 402 * deficit (encode c x.val) (encode c y.val) := by
  obtain ⟨A⟩ := exists_lcs_alignment (encode c x.val) (encode c y.val)
  have hx : (encode c x.val).length = M * P := by rw [length_encode, x.property]
  have hy : (encode c y.val).length = M * P := by rw [length_encode, y.property]
  let f := A.left.comp (Fin.castOrderIso hx).toOrderEmbedding
  let g := A.right.comp (Fin.castOrderIso hy).toOrderEmbedding
  have hfg : ∀ i,
      (encode c x.val).get (Fin.cast hx.symm (f i)) =
      (encode c y.val).get (Fin.cast hy.symm (g i)) := by
    intro i
    exact A.agree i
  have hadd := code_alignment_additive hP c hc x y f g hfg
  have hδ : deficit (encode c x.val) (encode c y.val) =
      M * P - lcs (encode c x.val) (encode c y.val) := by rw [deficit, hx]
  rw [← hδ] at hadd
  by_cases hr : deficit x.val y.val = 0
  · simp [hr]
  · have hmul : P ≤ P * deficit x.val y.val := Nat.le_mul_of_pos_right P (by omega)
    simp only [Nat.mul_assoc] at hthreshold hadd
    omega

theorem code_edit_comparison {M P a₀ : ℕ} (hP : 0 < P)
    (hthreshold : 4 * M * a₀ ≤ P) (c : α → Word Bool P)
    (hc : SegmentCode c a₀) (x y : Word α M) :
    (P : ℝ) / 804 * (ed x.val y.val : ℝ) ≤
      (ed (encode c x.val) (encode c y.val) : ℝ) ∧
    (ed (encode c x.val) (encode c y.val) : ℝ) ≤ (P : ℝ) * (ed x.val y.val : ℝ) ∧
    (P : ℝ) / 402 * (deficit x.val y.val : ℝ) ≤
      (deficit (encode c x.val) (encode c y.val) : ℝ) := by
  have hδ := code_deficit_comparison hP hthreshold c hc x y
  have hE := ed_le_twice_deficit (x.property.trans y.property.symm)
  have hδE := deficit_le_ed (encode c x.val) (encode c y.val)
  have hE' : (ed x.val y.val : ℝ) ≤ 2 * (deficit x.val y.val : ℝ) := by exact_mod_cast hE
  have hδ' : (P : ℝ) * (deficit x.val y.val : ℝ) ≤
      402 * (deficit (encode c x.val) (encode c y.val) : ℝ) := by exact_mod_cast hδ
  have hδE' : (deficit (encode c x.val) (encode c y.val) : ℝ) ≤
      (ed (encode c x.val) (encode c y.val) : ℝ) := by exact_mod_cast hδE
  refine ⟨?_, ?_, ?_⟩
  · have hP' : (0 : ℝ) ≤ P := Nat.cast_nonneg _
    nlinarith
  · exact_mod_cast ed_encode_le c x.val y.val
  · linarith

end TreeEdit

end OAI
