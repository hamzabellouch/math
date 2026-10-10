import OAI.Combinatorics.TreeEdit.SegmentComparison

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

lemma cycle_coordinates (m B n : ℕ) :
    n = n / (m * B) * (m * B) + (n / B % m) * B + n % B := by
  have h₁ := Nat.mod_add_div n B
  have h₂ := Nat.mod_add_div (n / B) m
  have hd : n / B / m = n / (m * B) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [hd] at h₂
  nlinarith

lemma split_cycle_gap {m B p p' q q' : ℕ} (hm : 2 ≤ m) (hB : 0 < B)
    (hp : p / (m * B) = p' / (m * B))
    (hq : q / (m * B) < q' / (m * B))
    (hc : p / B % m = q / B % m) (hc' : p' / B % m = q' / B % m) :
    q + p' + (m - 2) * B ≤ q' + p := by
  have hp0 := cycle_coordinates m B p
  have hp1 := cycle_coordinates m B p'
  have hq0 := cycle_coordinates m B q
  have hq1 := cycle_coordinates m B q'
  rw [hp, hc] at hp0
  rw [hc'] at hp1
  have hpm := Nat.mod_lt p hB
  have hpm' := Nat.mod_lt p' hB
  have hqm := Nat.mod_lt q hB
  have hqm' := Nat.mod_lt q' hB
  have ht := Nat.mul_le_mul_right (m * B) (Nat.succ_le_of_lt hq)
  have hm' : (m - 2) * B + 2 * B = m * B := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hm]
  simp only [Nat.succ_mul] at ht
  omega

lemma alignment_window_bound {β : Type*} {N : ℕ} (x y : List β)
    (f : Fin N ↪o Fin x.length) (g : Fin N ↪o Fin y.length)
    (hfg : ∀ i, x.get (f i) = y.get (g i))
    (s : Finset (Fin N)) {a b P Q : ℕ}
    (ha : a + P ≤ x.length) (hb : b + Q ≤ y.length)
    (hf : ∀ i ∈ s, a ≤ (f i).val ∧ (f i).val < a + P)
    (hg : ∀ i ∈ s, b ≤ (g i).val ∧ (g i).val < b + Q) :
    s.card ≤ lcs (segment x a P) (segment y b Q) := by
  let e := s.orderEmbOfFin rfl
  let X := segment x a P
  let Y := segment y b Q
  have hX : X.length = P := length_segment _ ha
  have hY : Y.length = Q := length_segment _ hb
  have hlo (i : Fin s.card) := hf (e i) (s.orderEmbOfFin_mem rfl i)
  have hro (i : Fin s.card) := hg (e i) (s.orderEmbOfFin_mem rfl i)
  let fl : Fin s.card → Fin X.length := fun i =>
    ⟨(f (e i)).val - a, by rw [hX]; have := hlo i; omega⟩
  let gr : Fin s.card → Fin Y.length := fun i =>
    ⟨(g (e i)).val - b, by rw [hY]; have := hro i; omega⟩
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
  simpa only [Nat.add_sub_of_le (hlo i).1, Nat.add_sub_of_le (hro i).1,
    List.get_eq_getElem] using hfg (e i)

lemma blockIndex_monotone {M P N : ℕ} (hP : 0 < P)
    (f : Fin N ↪o Fin (M * P)) : Monotone (fun i => blockIndex hP (f i)) := by
  intro i j hij
  exact Nat.div_le_div_right (f.monotone hij)

lemma card_block_fiber {M P N : ℕ} (hP : 0 < P)
    (f : Fin N ↪o Fin (M * P)) (a : Fin M) :
    (Finset.univ.filter (fun i => blockIndex hP (f i) = a)).card ≤ P := by
  classical
  let r : Fin N → Fin P := fun i => ⟨(f i).val % P, Nat.mod_lt _ hP⟩
  have hi : Set.InjOn r ↑(Finset.univ.filter (fun i => blockIndex hP (f i) = a)) := by
    intro i hi j hj he
    have hi' := congrArg Fin.val (Finset.mem_filter.mp hi).2
    have hj' := congrArg Fin.val (Finset.mem_filter.mp hj).2
    have hr := congrArg Fin.val he
    apply f.injective
    apply Fin.ext
    dsimp [blockIndex] at hi' hj'
    dsimp [r] at hr
    have hx := Nat.div_add_mod (f i).val P
    have hy := Nat.div_add_mod (f j).val P
    rw [hi'] at hx
    rw [hj'] at hy
    omega
  simpa using Finset.card_le_card_of_injOn r (fun _ _ => Finset.mem_univ _) hi

lemma blockIndex_window {M P : ℕ} (hP : 0 < P) {i : Fin (M * P)} {a : Fin M}
    (h : blockIndex hP i = a) : a.val * P ≤ i.val ∧ i.val < a.val * P + P := by
  have he := congrArg Fin.val h
  dsimp [blockIndex] at he
  have hm := Nat.mod_lt i.val hP
  have hd := Nat.div_add_mod i.val P
  rw [he, Nat.mul_comm P] at hd
  constructor <;> omega

lemma sum_block_losses {M P N : ℕ} (hP : 0 < P)
    (f : Fin N ↪o Fin (M * P)) :
    (∑ a : Fin M, (P - (Finset.univ.filter
      (fun i => blockIndex hP (f i) = a)).card)) = M * P - N := by
  rw [Finset.sum_tsub_distrib _ (fun a _ => card_block_fiber hP f a)]
  have he : (∑ a : Fin M, (Finset.univ.filter
      (fun i => blockIndex hP (f i) = a)).card) = N := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ)
      (f := fun i => blockIndex hP (f i)) (by simp)).symm
  simp [he]

lemma split_cycle_span_gap {m B T N : ℕ} (hm : 2 ≤ m) (hB : 0 < B)
    (f g : Fin N ↪o Fin (T * (m * B)))
    (hc : ∀ i, (f i).val / B % m = (g i).val / B % m)
    (a : Fin T) (hC : 0 < m * B)
    (hs : (Finset.univ.filter (fun i => blockIndex hC (f i) = a)).Nonempty)
    (hsp : blockIndex hC (g ((Finset.univ.filter
      (fun i => blockIndex hC (f i) = a)).min' hs)) ≠
      blockIndex hC (g ((Finset.univ.filter
      (fun i => blockIndex hC (f i) = a)).max' hs))) :
    (m - 2) * B ≤ (indexSpan g (Finset.univ.filter
      (fun i => blockIndex hC (f i) = a))).card -
        (Finset.univ.filter (fun i => blockIndex hC (f i) = a)).card := by
  let s := Finset.univ.filter (fun i => blockIndex hC (f i) = a)
  let i := s.min' hs
  let j := s.max' hs
  have hi : blockIndex hC (f i) = a := (Finset.mem_filter.mp (s.min'_mem hs)).2
  have hj : blockIndex hC (f j) = a := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have hij : i ≤ j := s.min'_le _ (s.max'_mem hs)
  have hg : (g i).val / (m * B) < (g j).val / (m * B) := by
    have hle := blockIndex_monotone hC g hij
    have hne : (blockIndex hC (g i)) ≠ blockIndex hC (g j) := hsp
    exact (show blockIndex hC (g i) < blockIndex hC (g j) from lt_of_le_of_ne hle hne)
  have hp : (f i).val / (m * B) = (f j).val / (m * B) :=
    congrArg Fin.val (hi.trans hj.symm)
  have hgap := split_cycle_gap hm hB hp hg (hc i) (hc j)
  have hfcard := card_le_indexSpan f s
  have hflen := span_length_formula f s hs
  have hglen := span_length_formula g s hs
  change (m - 2) * B ≤ (indexSpan g s).card - s.card
  dsimp [i, j] at hgap
  omega

lemma cycle_charging {m B T N : ℕ} (hm : 2 ≤ m) (hB : 0 < B)
    (f g : Fin N ↪o Fin (T * (m * B)))
    (hc : ∀ i, (f i).val / B % m = (g i).val / B % m)
    (δ : ℝ) (hδ : δ ≤ ((m - 2) * B : ℕ))
    (hsmall : ∀ (a b : Fin T),
      (∀ i ∈ Finset.univ.filter (fun i => blockIndex (by positivity : 0 < m * B) (f i) = a),
        blockIndex (by positivity : 0 < m * B) (g i) = b) →
      δ ≤ ((m * B - (Finset.univ.filter
          (fun i => blockIndex (by positivity : 0 < m * B) (f i) = a)).card : ℕ) : ℝ)) :
    (T : ℝ) * δ ≤ 2 * ((T * (m * B) - N : ℕ) : ℝ) := by
  classical
  have hC : 0 < m * B := by positivity
  let key := fun i => blockIndex hC (f i)
  let s := fun a : Fin T => Finset.univ.filter (fun i => key i = a)
  have hlocal (a : Fin T) : δ ≤ ((m * B - (s a).card : ℕ) : ℝ) +
      (((indexSpan g (s a)).card - (s a).card : ℕ) : ℝ) := by
    by_cases hs : (s a).Nonempty
    · by_cases he : blockIndex hC (g ((s a).min' hs)) =
          blockIndex hC (g ((s a).max' hs))
      · have hh := hsmall a (blockIndex hC (g ((s a).min' hs))) (by
          intro i hi
          have hl := blockIndex_monotone hC g ((s a).min'_le i hi)
          have hr := blockIndex_monotone hC g ((s a).le_max' i hi)
          change blockIndex hC (g i) ≤ blockIndex hC (g ((s a).max' hs)) at hr
          rw [← he] at hr
          exact le_antisymm hr hl)
        exact hh.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
      · have hg := split_cycle_span_gap hm hB f g hc a hC hs he
        have hh : δ ≤ (((indexSpan g (s a)).card - (s a).card : ℕ) : ℝ) :=
          hδ.trans (by exact_mod_cast hg)
        exact hh.trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
    · have he : s a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      rw [he]
      simp only [Finset.card_empty, Nat.sub_zero, indexSpan_empty, Nat.cast_zero, add_zero]
      exact hδ.trans (by exact_mod_cast Nat.mul_le_mul_right B (Nat.sub_le m 2))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin T))) => hlocal a)
  have htarget := sum_span_gaps_le g key (blockIndex_monotone hC f)
  have hsource := sum_block_losses hC f
  have htarget' : (∑ a : Fin T, (((indexSpan g (s a)).card - (s a).card : ℕ) : ℝ)) ≤
      ((T * (m * B) - N : ℕ) : ℝ) := by exact_mod_cast htarget
  have hsource' : (∑ a : Fin T, ((m * B - (s a).card : ℕ) : ℝ)) =
      ((T * (m * B) - N : ℕ) : ℝ) := by exact_mod_cast hsource
  simp only [Finset.sum_add_distrib] at hsum
  rw [hsource'] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

end TreeEdit

end OAI
