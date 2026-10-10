import OAI.Combinatorics.TreeEdit.EditMetric

namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

structure Alignment (x y : List α) (n : ℕ) where
  left : Fin n ↪o Fin x.length
  right : Fin n ↪o Fin y.length
  agree : ∀ i, x.get (left i) = y.get (right i)

namespace Alignment

variable {n : ℕ}

theorem le_lcs (a : Alignment x y n) : n ≤ lcs x y := by
  let z := List.ofFn (fun i => x.get (a.left i))
  have hz : z.length = n := List.length_ofFn
  have hl : z.Sublist x := by
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨(Fin.castOrderIso hz).toOrderEmbedding.comp a.left, ?_⟩
    intro i
    simp [z, Fin.cast]
  have hr : z.Sublist y := by
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨(Fin.castOrderIso hz).toOrderEmbedding.comp a.right, ?_⟩
    intro i
    simpa [z, Fin.cast] using a.agree (Fin.cast hz i)
  exact hz ▸ length_le_lcs hl hr

def restrict (a : Alignment x y n) {k : ℕ} (f : Fin k ↪o Fin n) : Alignment x y k where
  left := f.comp a.left
  right := f.comp a.right
  agree i := a.agree (f i)

end Alignment

theorem exists_lcs_alignment (x y : List α) : Nonempty (Alignment x y (lcs x y)) := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hy
  refine ⟨⟨(Fin.castOrderIso hz.symm).toOrderEmbedding.comp f,
    (Fin.castOrderIso hz.symm).toOrderEmbedding.comp g, ?_⟩⟩
  intro i
  exact (hf (Fin.cast hz.symm i)).symm.trans (hg (Fin.cast hz.symm i))

theorem strictMono_fin_gap {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f)
    (i j : Fin n) (hij : i ≤ j) : f i + (j.val - i.val) ≤ f j := by
  have aux : ∀ (b d : ℕ) (h : b + d < n),
      f ⟨b, by omega⟩ + d ≤ f ⟨b + d, h⟩ := by
    intro b d
    induction d with
    | zero => intro h; simp
    | succ d ih =>
        intro h
        have hi := ih (by omega)
        have hh : f ⟨b + d, by omega⟩ < f ⟨b + (d + 1), h⟩ := hf (by simp)
        omega
  have he : i.val + (j.val - i.val) = j.val := Nat.add_sub_of_le hij
  simpa only [he] using aux i.val (j.val - i.val) (by omega)

theorem div_strict_of_equal_residue {n P : ℕ} (hP : 0 < P)
    (f : Fin n → ℕ) (hf : StrictMono f) {i j : Fin n}
    (hij : i < j) (hmod : i.val % P = j.val % P) : f i / P < f j / P := by
  have hid := Nat.mod_add_div i.val P
  have hjd := Nat.mod_add_div j.val P
  have hq : i.val / P < j.val / P := by
    by_contra hn
    have hmul := Nat.mul_le_mul_left P (Nat.le_of_not_gt hn)
    have : j.val ≤ i.val := by omega
    exact (not_le_of_gt hij) this
  have hmul := Nat.mul_le_mul_left P (Nat.succ_le_of_lt hq)
  have hgap : P ≤ j.val - i.val := by
    rw [Nat.mul_succ] at hmul
    omega
  have hg := strictMono_fin_gap f hf i j (le_of_lt hij)
  have h : f i + P ≤ f j := by omega
  have hd := Nat.div_le_div_right (c := P) h
  rw [Nat.add_div_right _ hP] at hd
  omega

def blockIndex {M P : ℕ} (hP : 0 < P) (i : Fin (M * P)) : Fin M :=
  ⟨i.val / P, (Nat.div_lt_iff_lt_mul hP).mpr i.isLt⟩

theorem equal_label_alignment_bound {M P N : ℕ} (hP : 0 < P)
    (x y : Word α M) (f g : Fin N ↪o Fin (M * P))
    (heq : ∀ i, x.val.get (Fin.cast x.property.symm (blockIndex hP (f i))) =
        y.val.get (Fin.cast y.property.symm (blockIndex hP (g i)))) :
    N ≤ P * lcs x.val y.val := by
  classical
  let residue : Fin N → Fin P := fun i => ⟨i.val % P, Nat.mod_lt _ hP⟩
  have hclass : ∀ r : Fin P,
      (Finset.univ.filter (fun i : Fin N => residue i = r)).card ≤ lcs x.val y.val := by
    intro r
    let s := Finset.univ.filter (fun i : Fin N => residue i = r)
    let e := s.orderEmbOfFin rfl
    have hm (i : Fin s.card) : residue (e i) = r :=
      (Finset.mem_filter.mp (s.orderEmbOfFin_mem rfl i)).2
    have hleft : StrictMono (fun i : Fin s.card =>
        Fin.cast x.property.symm (blockIndex hP (f (e i)))) := by
      intro i j hij
      change (f (e i)).val / P < (f (e j)).val / P
      apply div_strict_of_equal_residue hP (fun i => (f i).val)
        (Fin.val_strictMono.comp f.strictMono) (e.strictMono hij)
      exact congrArg Fin.val ((hm i).trans (hm j).symm)
    have hright : StrictMono (fun i : Fin s.card =>
        Fin.cast y.property.symm (blockIndex hP (g (e i)))) := by
      intro i j hij
      change (g (e i)).val / P < (g (e j)).val / P
      apply div_strict_of_equal_residue hP (fun i => (g i).val)
        (Fin.val_strictMono.comp g.strictMono) (e.strictMono hij)
      exact congrArg Fin.val ((hm i).trans (hm j).symm)
    exact Alignment.le_lcs ⟨OrderEmbedding.ofStrictMono _ hleft,
      OrderEmbedding.ofStrictMono _ hright, fun i => heq (e i)⟩
  have hpartition : N = ∑ r : Fin P, (Finset.univ.filter
      (fun i : Fin N => residue i = r)).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (f := residue) (by simp))
  rw [hpartition]
  calc
    _ ≤ ∑ _r : Fin P, lcs x.val y.val := Finset.sum_le_sum (fun r _ => hclass r)
    _ = P * lcs x.val y.val := by simp

noncomputable def indexSpan {N L : ℕ} (f : Fin N ↪o Fin L) (s : Finset (Fin N)) :
    Finset (Fin L) :=
  if h : s.Nonempty then Finset.Icc (f (s.min' h)) (f (s.max' h)) else ∅

@[simp] theorem indexSpan_empty {N L : ℕ} (f : Fin N ↪o Fin L) :
    indexSpan f ∅ = ∅ := by simp [indexSpan]

theorem mem_indexSpan {N L : ℕ} (f : Fin N ↪o Fin L) {s : Finset (Fin N)}
    {i : Fin N} (hi : i ∈ s) : f i ∈ indexSpan f s := by
  have hs : s.Nonempty := ⟨i, hi⟩
  simp only [indexSpan, dite_eq_left hs, Finset.mem_Icc]
  exact ⟨f.monotone (s.min'_le i hi), f.monotone (s.le_max' i hi)⟩

theorem card_le_indexSpan {N L : ℕ} (f : Fin N ↪o Fin L) (s : Finset (Fin N)) :
    s.card ≤ (indexSpan f s).card := by
  exact Finset.card_le_card_of_injOn f (fun _ hi => mem_indexSpan f hi) f.injective.injOn

theorem indexSpan_disjoint {N L K : ℕ} (f : Fin N ↪o Fin L)
    (key : Fin N → Fin K) (hk : Monotone key) {a b : Fin K} (hab : a ≠ b) :
    Disjoint (indexSpan f (Finset.univ.filter (fun i => key i = a)))
      (indexSpan f (Finset.univ.filter (fun i => key i = b))) := by
  classical
  let sa := Finset.univ.filter (fun i => key i = a)
  let sb := Finset.univ.filter (fun i => key i = b)
  change Disjoint (indexSpan f sa) (indexSpan f sb)
  by_cases ha : sa.Nonempty
  · by_cases hb : sb.Nonempty
    · have hamin : key (sa.min' ha) = a :=
        (Finset.mem_filter.mp (sa.min'_mem ha)).2
      have hamax : key (sa.max' ha) = a :=
        (Finset.mem_filter.mp (sa.max'_mem ha)).2
      have hbmin : key (sb.min' hb) = b :=
        (Finset.mem_filter.mp (sb.min'_mem hb)).2
      have hbmax : key (sb.max' hb) = b :=
        (Finset.mem_filter.mp (sb.max'_mem hb)).2
      refine Finset.disjoint_left.mpr ?_
      intro p hp hq
      simp only [indexSpan, dite_eq_left ha, dite_eq_left hb, Finset.mem_Icc] at hp hq
      rcases lt_or_gt_of_ne hab with hab | hba
      · have hh : sa.max' ha < sb.min' hb := by
          by_contra hn
          have := hk (le_of_not_gt hn)
          rw [hbmin, hamax] at this
          exact (not_le_of_gt hab) this
        exact (not_le_of_gt (f.strictMono hh)) (hq.1.trans hp.2)
      · have hh : sb.max' hb < sa.min' ha := by
          by_contra hn
          have := hk (le_of_not_gt hn)
          rw [hamin, hbmax] at this
          exact (not_le_of_gt hba) this
        exact (not_le_of_gt (f.strictMono hh)) (hp.1.trans hq.2)
    · simp [indexSpan, hb]
  · simp [indexSpan, ha]

theorem sum_span_card_le {N L K : ℕ} (f : Fin N ↪o Fin L)
    (key : Fin N → Fin K) (hk : Monotone key) :
    (∑ k : Fin K, (indexSpan f (Finset.univ.filter (fun i => key i = k))).card) ≤ L := by
  have hd : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint
      (fun k => indexSpan f (Finset.univ.filter (fun i => key i = k))) := by
    intro a _ b _ hab
    exact indexSpan_disjoint f key hk hab
  rw [← Finset.card_biUnion hd]
  simpa using Finset.card_le_univ
    (Finset.univ.biUnion (fun k => indexSpan f (Finset.univ.filter (fun i => key i = k))))

theorem sum_span_gaps_le {N L K : ℕ} (f : Fin N ↪o Fin L)
    (key : Fin N → Fin K) (hk : Monotone key) :
    (∑ k : Fin K, ((indexSpan f (Finset.univ.filter (fun i => key i = k))).card -
      (Finset.univ.filter (fun i => key i = k)).card)) ≤ L - N := by
  rw [Finset.sum_tsub_distrib _ (fun _ _ => card_le_indexSpan f _)]
  have he : (∑ k : Fin K, (Finset.univ.filter (fun i => key i = k)).card) = N := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (f := key) (by simp)).symm
  rw [he]
  exact Nat.sub_le_sub_right (sum_span_card_le f key hk) N

def blockPairKey {M P N : ℕ} (hP : 0 < P) (f g : Fin N ↪o Fin (M * P))
    (i : Fin N) : Fin (2 * M) :=
  ⟨(blockIndex hP (f i)).val + (blockIndex hP (g i)).val, by
    have := (blockIndex hP (f i)).isLt
    have := (blockIndex hP (g i)).isLt
    omega⟩

theorem blockPairKey_monotone {M P N : ℕ} (hP : 0 < P)
    (f g : Fin N ↪o Fin (M * P)) : Monotone (blockPairKey hP f g) := by
  intro i j hij
  change (f i).val / P + (g i).val / P ≤ (f j).val / P + (g j).val / P
  exact Nat.add_le_add (Nat.div_le_div_right (f.monotone hij))
    (Nat.div_le_div_right (g.monotone hij))

theorem blockPairKey_eq_iff {M P N : ℕ} (hP : 0 < P)
    (f g : Fin N ↪o Fin (M * P)) (i j : Fin N) :
    blockPairKey hP f g i = blockPairKey hP f g j ↔
      blockIndex hP (f i) = blockIndex hP (f j) ∧
      blockIndex hP (g i) = blockIndex hP (g j) := by
  constructor
  · intro h
    have he := congrArg Fin.val h
    dsimp [blockPairKey] at he
    rcases le_total i j with hij | hji
    · have hfl := Nat.div_le_div_right (c := P) (f.monotone hij)
      have hgl := Nat.div_le_div_right (c := P) (g.monotone hij)
      constructor <;> apply Fin.ext <;> dsimp [blockIndex] at * <;> omega
    · have hfl := Nat.div_le_div_right (c := P) (f.monotone hji)
      have hgl := Nat.div_le_div_right (c := P) (g.monotone hji)
      constructor <;> apply Fin.ext <;> dsimp [blockIndex] at * <;> omega
  · rintro ⟨hf, hg⟩
    apply Fin.ext
    dsimp [blockPairKey]
    rw [hf, hg]

theorem block_span_gap_budget {M P N : ℕ} (hP : 0 < P)
    (f g : Fin N ↪o Fin (M * P)) :
    (∑ k : Fin (2 * M),
      ((indexSpan f (Finset.univ.filter (fun i => blockPairKey hP f g i = k))).card -
        (Finset.univ.filter (fun i => blockPairKey hP f g i = k)).card +
       ((indexSpan g (Finset.univ.filter (fun i => blockPairKey hP f g i = k))).card -
        (Finset.univ.filter (fun i => blockPairKey hP f g i = k)).card))) ≤
      2 * (M * P - N) := by
  rw [Finset.sum_add_distrib]
  have hl := sum_span_gaps_le f _ (blockPairKey_monotone hP f g)
  have hr := sum_span_gaps_le g _ (blockPairKey_monotone hP f g)
  omega

end TreeEdit

end OAI
