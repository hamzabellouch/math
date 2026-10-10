import OAI.Computability.Superstring.Input

namespace OAI

namespace Superstring

namespace Hierarchical

variable {α : Type}

/-- The least positive period is explicit, as required for primitive groups. -/
structure Primitive (A : ℤ → α) (p : ℕ) : Prop where
  positive : 0 < p
  periodic : Function.Periodic A (p : ℤ)
  least : ∀ n : ℕ, 0 < n → Function.Periodic A (n : ℤ) → p ≤ n

/-- Existence from any positive turn length. -/
theorem exists_primitive {A : ℤ → α} {P : ℕ} (hP : 0 < P)
    (hper : Function.Periodic A (P : ℤ)) : ∃ p, Primitive A p := by
  classical
  have hex : ∃ n : ℕ, 0 < n ∧ Function.Periodic A (n : ℤ) := ⟨P, hP, hper⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro n hn hnp
  exact Nat.find_min' hex ⟨hn, hnp⟩

/-- All translational symmetries, including negative ones, are precisely the
multiples of the primitive period. -/
theorem Primitive.period_iff_dvd {A : ℤ → α} {p : ℕ} (h : Primitive A p) (d : ℤ) :
    Function.Periodic A d ↔ (p : ℤ) ∣ d := by
  constructor
  · intro hd
    have hpz : (0 : ℤ) < p := by have := h.positive; omega
    have hm0 := Int.emod_nonneg d (show (p : ℤ) ≠ 0 by omega)
    have hml := Int.emod_lt_of_pos d hpz
    have hmod : Function.Periodic A (d % (p : ℤ)) := by
      have hh := hd.sub_period (h.periodic.int_mul (d / p))
      have he : d - (d / (p : ℤ)) * p = d % p := by
        have := Int.emod_add_ediv_mul d (p : ℤ)
        omega
      simpa only [Int.cast_id, he] using hh
    have hmz : d % (p : ℤ) = 0 := by
      by_contra hz
      have hnat : 0 < (d % (p : ℤ)).toNat := by omega
      have he : (((d % (p : ℤ)).toNat : ℕ) : ℤ) = d % p := by omega
      have hh := h.least _ hnat (he ▸ hmod)
      omega
    exact Int.dvd_of_emod_eq_zero hmz
  · rintro ⟨q, rfl⟩
    simpa only [Int.cast_id, mul_comm] using h.periodic.int_mul q

/-- There is exactly one identical full-text alignment in a primitive turn. -/
theorem Primitive.alignment_unique {A : ℤ → α} {p : ℕ} (h : Primitive A p)
    {i j : ℤ} (hi : 0 ≤ i) (hip : i < p) (hj : 0 ≤ j) (hjp : j < p)
    (heq : ∀ x, A (x + i) = A (x + j)) : i = j := by
  have hper : Function.Periodic A (i - j) := by
    intro x
    have hh := heq (x - j)
    convert hh using 1 <;> congr 1 <;> omega
  obtain ⟨q, hq⟩ := (h.period_iff_dvd _).mp hper
  have hpz : (0 : ℤ) < p := by have := h.positive; omega
  have h0 : q = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have : (p : ℤ) * q ≤ -(p : ℤ) := by nlinarith
      omega
    · have : (p : ℤ) ≤ (p : ℤ) * q := by nlinarith
      omega
  simp only [h0, mul_zero] at hq
  omega

end Hierarchical

namespace OrderStats

variable {β : Type} [LinearOrder β] {n : ℕ}

def sortedList (f : Fin n → β) : List β :=
  (List.ofFn f).mergeSort (fun a b => decide (a ≤ b))

@[simp] theorem sortedList_length (f : Fin n → β) : (sortedList f).length = n := by
  simp only [sortedList, List.length_mergeSort, List.length_ofFn]

def order (f : Fin n → β) (i : Fin n) : β :=
  (sortedList f).get ⟨i.val, by simpa only [sortedList_length] using i.isLt⟩

theorem monotone_order (f : Fin n → β) : Monotone (order f) := by
  intro i j hij
  exact List.sortedLE_mergeSort.monotone_get (show
    (⟨i.val, by simpa only [sortedList_length] using i.isLt⟩ : Fin (sortedList f).length) ≤
      ⟨j.val, by simpa only [sortedList_length] using j.isLt⟩ from hij)

theorem ofFn_order (f : Fin n → β) : List.ofFn (order f) = sortedList f := by
  apply List.ext_getElem (by simp only [List.length_ofFn, sortedList_length])
  intro i hi hi'
  simp only [List.getElem_ofFn, order, List.get_eq_getElem]

theorem order_mem (f : Fin n → β) (i : Fin n) : ∃ j, f j = order f i := by
  apply List.mem_ofFn.mp
  apply (List.mergeSort_perm (List.ofFn f) (fun a b => decide (a ≤ b))).mem_iff.mp
  exact List.get_mem ..

/-- Counting a finite function's values is the same on its explicit list. -/
theorem countP_ofFn {γ : Type} (P : γ → Bool) (f : Fin n → γ) :
    (List.ofFn f).countP P = ∑ i : Fin n, if P (f i) then 1 else 0 := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.countP_nil, Fin.sum_univ_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, Fin.sum_univ_succ]
    rw [ih]
    omega

/-- Sorting preserves all value multiplicities, including repetitions. -/
theorem card_filter_order (f : Fin n → β) (P : β → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i => P (order f i))).card =
      (Finset.univ.filter (fun i => P (f i))).card := by
  have hh := (List.mergeSort_perm (List.ofFn f) (fun a b => decide (a ≤ b))).countP_eq
    (fun a => decide (P a))
  change (sortedList f).countP (fun a => decide (P a)) = _ at hh
  rw [← ofFn_order f, countP_ofFn, countP_ofFn] at hh
  simpa only [Finset.card_filter, decide_eq_true_eq] using hh

/-- Order statistics characterized by cumulative counts. -/
theorem monotone_count_iff {f : Fin n → β} (hm : Monotone f) (i : Fin n) (t : β) :
    f i ≤ t ↔ i.val < (Finset.univ.filter (fun j => f j ≤ t)).card := by
  constructor
  · intro hit
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j => f j ≤ t) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hm (Finset.mem_Iic.mp hj)).trans hit⟩
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hh
    omega
  · intro hcard
    by_contra hnot
    have hsub : (Finset.univ.filter (fun j => f j ≤ t)) ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hnotlt
      have hle : i ≤ j := le_of_not_gt hnotlt
      exact hnot ((hm hle).trans (Finset.mem_filter.mp hj).2)
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hh
    omega

theorem order_le_iff (f : Fin n → β) (i : Fin n) (t : β) :
    order f i ≤ t ↔ i.val < (Finset.univ.filter (fun j => f j ≤ t)).card := by
  rw [monotone_count_iff (monotone_order f), card_filter_order f (fun a => a ≤ t)]

/-- A coordinatewise increasing matching remains increasing after sorting. -/
theorem order_le_order {f g : Fin n → β} (h : ∀ i, f i ≤ g i) (i : Fin n) :
    order f i ≤ order g i := by
  apply (order_le_iff f i _).mpr
  apply lt_of_lt_of_le ((order_le_iff g i _).mp le_rfl)
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h j).trans (Finset.mem_filter.mp hj).2⟩

theorem order_eq_of_counts {f g : Fin n → β}
    (h : ∀ t, (Finset.univ.filter (fun j => f j ≤ t)).card =
      (Finset.univ.filter (fun j => g j ≤ t)).card) (i : Fin n) : order f i = order g i := by
  have he : ∀ t, order f i ≤ t ↔ order g i ≤ t := by
    intro t
    rw [order_le_iff, order_le_iff, h t]
  exact le_antisymm ((he _).mpr le_rfl) ((he _).mp le_rfl)

theorem order_add (f : Fin n → ℤ) (c : ℤ) (i : Fin n) :
    order (fun j => f j + c) i = order f i + c := by
  have he : ∀ t, order (fun j => f j + c) i ≤ t ↔ order f i + c ≤ t := by
    intro t
    rw [← le_sub_iff_add_le, order_le_iff, order_le_iff]
    have hh : Finset.univ.filter (fun j => f j + c ≤ t) =
        Finset.univ.filter (fun j => f j ≤ t - c) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hh]
  exact le_antisymm ((he _).mpr le_rfl) ((he _).mp le_rfl)

/-- No artificial window is introduced by sorting matched passages. -/
theorem sorted_window {entry exit : Fin n → β} (i : Fin n) {e : β}
    (hentry : order entry i ≤ e) (hexit : e ≤ order exit i) :
    ∃ j, entry j ≤ e ∧ e ≤ exit j := by
  by_contra hno
  push Not at hno
  have hsub : Finset.univ.filter (fun j => entry j ≤ e) ⊆
      Finset.univ.filter (fun j => exit j < e) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hno j (Finset.mem_filter.mp hj).2⟩
  have hc := Finset.card_le_card hsub
  have hl := (order_le_iff entry i e).mp hentry
  have hs : Finset.univ.filter (fun j => order exit j < e) ⊆ Finset.Iio i := by
    intro j hj
    apply Finset.mem_Iio.mpr
    by_contra hnot
    have hh := monotone_order exit (le_of_not_gt hnot)
    exact (not_lt_of_ge (hexit.trans hh)) (Finset.mem_filter.mp hj).2
  have hh := Finset.card_le_card hs
  rw [Fin.card_Iio, card_filter_order exit (fun a => a < e)] at hh
  omega

/-- Exact upward-unit-edge conservation. For each height, sorting preserves the
number of vertical intervals traversing it, not just the set of vertices. -/
theorem sorted_edge_count {entry exit : Fin n → ℤ} (h : ∀ j, entry j ≤ exit j) (e : ℤ) :
    (Finset.univ.filter (fun j => order entry j ≤ e ∧ e < order exit j)).card =
      (Finset.univ.filter (fun j => entry j ≤ e ∧ e < exit j)).card := by
  have count (a b : Fin n → ℤ) (hab : ∀ j, a j ≤ b j) :
      (Finset.univ.filter (fun j => a j ≤ e ∧ e < b j)).card +
        (Finset.univ.filter (fun j => b j ≤ e)).card =
          (Finset.univ.filter (fun j => a j ≤ e)).card := by
    have heq : Finset.univ.filter (fun j => a j ≤ e) =
        (Finset.univ.filter (fun j => a j ≤ e ∧ e < b j)) ∪
          (Finset.univ.filter (fun j => b j ≤ e)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro ha
        by_cases hb : e < b j
        · exact Or.inl ⟨ha, hb⟩
        · exact Or.inr (le_of_not_gt hb)
      · rintro (⟨ha, _⟩ | hb)
        · exact ha
        · exact (hab j).trans hb
    have hd : Disjoint (Finset.univ.filter (fun j => a j ≤ e ∧ e < b j))
        (Finset.univ.filter (fun j => b j ≤ e)) := by
      apply Finset.disjoint_left.mpr
      intro j hj hk
      exact (not_lt_of_ge (Finset.mem_filter.mp hk).2) (Finset.mem_filter.mp hj).2.2
    rw [heq, Finset.card_union_of_disjoint hd]
  have ha := count entry exit h
  have hb := count (order entry) (order exit) (order_le_order h)
  rw [card_filter_order exit (fun a => a ≤ e),
    card_filter_order entry (fun a => a ≤ e)] at hb
  omega

end OrderStats

namespace PrefixMatching

variable {α ι κ : Type} [DecidableEq α] [Fintype ι] [Fintype κ]

/-- A direct laminar Hall argument. Prefix requests can be assigned distinct
extensions precisely when every prefix subtree has enough capacity. -/
theorem hall (request : ι → List α) (supply : κ → List α)
    (hcapacity : ∀ w, (Finset.univ.filter (fun i => w <+: request i)).card ≤
      (Finset.univ.filter (fun j => w <+: supply j)).card) :
    ∃ f : ι → κ, Function.Injective f ∧ ∀ i, request i <+: supply (f i) := by
  classical
  let t : ι → Finset κ := fun i => Finset.univ.filter (fun j => request i <+: supply j)
  have hhall (s : Finset ι) : s.card ≤ (s.biUnion t).card := by
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      by_cases hs : s.Nonempty
      · obtain ⟨i, hi, hmin⟩ := s.exists_min_image (fun i => (request i).length) hs
        let a := s.filter (fun j => request i <+: request j)
        let b := s.filter (fun j => ¬ request i <+: request j)
        have hbsub : b ⊂ s := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
          intro he
          have : i ∈ b := he.symm ▸ hi
          exact (Finset.mem_filter.mp this).2 (List.prefix_refl _)
        have hab : a ∪ b = s := by
          ext j
          simp only [a, b, Finset.mem_union, Finset.mem_filter]
          tauto
        have hd : Disjoint a b := by
          apply Finset.disjoint_left.mpr
          intro j hj hk
          exact (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hj).2
        have hacap : a.card ≤ (t i).card := by
          apply le_trans (Finset.card_le_card ?_) (hcapacity (request i))
          intro j hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
        have htind : Disjoint (t i) (b.biUnion t) := by
          apply Finset.disjoint_left.mpr
          intro j hji hjb
          obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp hjb
          have hprei : request i <+: supply j := (Finset.mem_filter.mp hji).2
          have hprek : request k <+: supply j := (Finset.mem_filter.mp hjk).2
          exact (Finset.mem_filter.mp hk).2
            (List.prefix_of_prefix_length_le hprei hprek
              (hmin k (Finset.mem_filter.mp hk).1))
        have hsupply : (t i) ∪ b.biUnion t ⊆ s.biUnion t := by
          intro j hj
          rcases Finset.mem_union.mp hj with hj | hj
          · exact Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
          · obtain ⟨k, hk, hj⟩ := Finset.mem_biUnion.mp hj
            exact Finset.mem_biUnion.mpr ⟨k, (Finset.mem_filter.mp hk).1, hj⟩
        have hbc := ih b hbsub
        have hsc := Finset.card_le_card hsupply
        rw [Finset.card_union_of_disjoint htind] at hsc
        have hcard := Finset.card_union_of_disjoint hd
        rw [hab] at hcard
        omega
      · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        simp only [Finset.card_empty, Nat.zero_le]
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hhall
  exact ⟨f, hf, fun i => (Finset.mem_filter.mp (hmem i)).2⟩

/-- On equal finite token sets the matching is a permutation. -/
theorem permutation (request supply : ι → List α)
    (hcapacity : ∀ w, (Finset.univ.filter (fun i => w <+: request i)).card ≤
      (Finset.univ.filter (fun j => w <+: supply j)).card) :
    ∃ f : Equiv.Perm ι, ∀ i, request i <+: supply (f i) := by
  obtain ⟨f, hf, hp⟩ := hall request supply hcapacity
  exact ⟨Equiv.ofBijective f ⟨hf, (Finite.injective_iff_surjective).mp hf⟩, hp⟩

end PrefixMatching

end Superstring

end OAI
