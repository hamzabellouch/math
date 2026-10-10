import OAI.Combinatorics.Ramsey.CycleClique.Construction.GlobalLongest
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CycleTwoPaths
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TriangleFacts

namespace OAI

/-! Cycle surgery for the alpha-two specialization of Chvátal–Erdős.
-/

namespace CycleClique.Construction
theorem ce_cycle_to_indexed {V : Type*} {H : SimpleGraph V} {r : ℕ}
    {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i))) : IsIndexedPath H c := by
  refine ⟨hc, fun i => ?_⟩
  have hn : cycleNext i.castSucc = i.succ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.succ.isLt
  simpa only [hn] using he i.castSucc

theorem ce_cycle_rotate {V : Type*} {H : SimpleGraph V} {r : ℕ}
    {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i))) (a : Fin (r + 1)) :
    Function.Injective (fun i => c (i + a)) ∧
      ∀ i, H.Adj (c (i + a)) (c (cycleNext i + a)) := by
  refine ⟨hc.comp (fun _ _ h => add_right_cancel h), fun i => ?_⟩
  simpa only [cycleNext_eq_add_one, add_assoc, add_comm 1 a] using he (i + a)

/-- Replacing a cycle edge by an exterior path retains every cycle vertex. -/
theorem ce_consecutive_ear_cycle {V : Type*} {H : SimpleGraph V} {r l : ℕ}
    (hl : 2 ≤ l) {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    (a : Fin (r + 1)) {g : Fin (l + 1) → V} (hg : IsIndexedPath H g)
    (hg0 : g 0 = c a) (hgl : g (Fin.last l) = c (a + 1))
    (hdis : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
      ∀ j : Fin (r + 1), c j ≠ g i) : HasCycle H (r + l) := by
  let f : Fin (r + 1) → V := fun i => c (i + (a + 1))
  have hf : IsIndexedPath H f :=
    ce_cycle_to_indexed (ce_cycle_rotate hc he (a + 1)).1
      (ce_cycle_rotate hc he (a + 1)).2
  have hlast : (Fin.last r : Fin (r + 1)) + 1 = 0 := by
    rw [← cycleNext_eq_add_one]
    apply Fin.ext
    simp [cycleNext]
  have hflast : f (Fin.last r) = c a := by
    dsimp [f]
    congr 1
    calc
      Fin.last r + (a + 1) = (Fin.last r + 1) + a := by abel
      _ = a := by rw [hlast, zero_add]
  apply cycle_of_two_indexed_paths hl f g hf hg
  · exact hg0.trans hflast.symm
  · simpa only [f, zero_add] using hgl
  · intro i hi hil j
    exact hdis i hi hil (j + (a + 1))

private def ceChordIndex {r : ℕ} (j : Fin r) (i : Fin (r + 1)) : Fin (r + 1) :=
  ⟨if i.val < j.val then j.val - i.val else if i.val < r then i.val + 1 else 0,
    by split_ifs <;> have := j.isLt <;> omega⟩

private theorem ceChordIndex_injective {r : ℕ} (j : Fin r) :
    Function.Injective (ceChordIndex j) := by
  intro i k h
  have hv := congrArg Fin.val h
  dsimp [ceChordIndex] at hv
  apply Fin.ext
  have hi := i.isLt
  have hk := k.isLt
  have hj := j.isLt
  split_ifs at hv <;> omega

private theorem ce_cycle_step {V : Type*} {H : SimpleGraph V} {r : ℕ}
    {c : Fin (r + 1) → V} (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    {i j : Fin (r + 1)} (h : i.val + 1 = j.val) : H.Adj (c i) (c j) := by
  have hn : cycleNext i = j := by
    apply Fin.ext
    change (i.val + 1) % (r + 1) = j.val
    rw [h, Nat.mod_eq_of_lt j.isLt]
  simpa only [hn] using he i

/-- The successor chord joins the two complementary portions of the old cycle. -/
theorem ce_successor_chord_path {V : Type*} {H : SimpleGraph V} {r : ℕ}
    {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    (j : Fin r) (hj : 0 < j.val)
    (hchord : H.Adj (c ⟨1, by omega⟩) (c j.succ)) :
    ∃ f : Fin (r + 1) → V, IsIndexedPath H f ∧
      f 0 = c j.castSucc ∧ f (Fin.last r) = c 0 ∧
      Set.range f = Set.range c := by
  let f := c ∘ ceChordIndex j
  have hpath : IsIndexedPath H f := by
    refine ⟨hc.comp (ceChordIndex_injective j), fun i => ?_⟩
    by_cases hb : i.val + 1 < j.val
    · apply (ce_cycle_step he ?_).symm
      simp only [ceChordIndex, Fin.val_succ, Fin.val_castSucc]
      split_ifs <;> omega
    · by_cases heq : i.val + 1 = j.val
      · have hl : ceChordIndex j i.castSucc = ⟨1, by omega⟩ := by
          apply Fin.ext
          simp only [ceChordIndex, Fin.val_castSucc]
          split_ifs <;> omega
        have hr : ceChordIndex j i.succ = j.succ := by
          apply Fin.ext
          simp only [ceChordIndex, Fin.val_succ]
          split_ifs <;> have := j.isLt <;> omega
        simpa only [f, Function.comp_apply, hl, hr] using hchord
      · by_cases hlast : i.val + 1 = r
        · have hl : ceChordIndex j i.castSucc = Fin.last r := by
            apply Fin.ext
            simp only [ceChordIndex, Fin.val_castSucc, Fin.val_last]
            split_ifs <;> have := j.isLt <;> omega
          have hr : ceChordIndex j i.succ = 0 := by
            apply Fin.ext
            simp only [ceChordIndex, Fin.val_succ, Fin.val_zero]
            split_ifs <;> have := j.isLt <;> omega
          have hn : cycleNext (Fin.last r) = 0 := by
            apply Fin.ext
            simp [cycleNext]
          simpa only [f, Function.comp_apply, hl, hr, hn] using he (Fin.last r)
        · apply ce_cycle_step he
          simp only [ceChordIndex, Fin.val_succ, Fin.val_castSucc]
          split_ifs <;> have := i.isLt <;> omega
  refine ⟨f, hpath, ?_, ?_, ?_⟩
  · apply congrArg c
    apply Fin.ext
    simp [ceChordIndex, hj]
  · apply congrArg c
    apply Fin.ext
    simp [ceChordIndex, Nat.not_lt.mpr j.isLt.le]
  · have hsurj := Finite.surjective_of_injective (ceChordIndex_injective j)
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨ceChordIndex j i, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := hsurj i
      exact ⟨k, by simp only [f, Function.comp_apply, hk]⟩

theorem ce_chord_ear_cycle {V : Type*} {H : SimpleGraph V} {r l : ℕ}
    (hl : 2 ≤ l) {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i))) (j : Fin r) (hj : 0 < j.val)
    (hchord : H.Adj (c ⟨1, by omega⟩) (c j.succ))
    {g : Fin (l + 1) → V} (hg : IsIndexedPath H g)
    (hg0 : g 0 = c 0) (hgl : g (Fin.last l) = c j.castSucc)
    (hdis : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
      ∀ k : Fin (r + 1), c k ≠ g i) : HasCycle H (r + l) := by
  obtain ⟨f, hf, hf0, hfl, hrange⟩ := ce_successor_chord_path hc he j hj hchord
  apply cycle_of_two_indexed_paths hl f g hf hg (hg0.trans hfl.symm) (hgl.trans hf0.symm)
  intro i hi hil k
  obtain ⟨q, hq⟩ := hrange.subset ⟨k, rfl⟩
  exact fun h => hdis i hi hil q (hq.trans h)

theorem ce_indexedPath_tail {V : Type*} {H : SimpleGraph V} {r : ℕ}
    {g : Fin (r + 2) → V} (hg : IsIndexedPath H g) :
    IsIndexedPath H (fun i : Fin (r + 1) => g i.succ) := by
  refine ⟨hg.1.comp (Fin.succ_injective _), fun i => ?_⟩
  have hi : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  simpa only [hi] using hg.2 i.succ

/-- Reverse the noninitial part of an ear and attach a new final vertex.
Every internal vertex of the resulting path was internal to the original ear. -/
theorem ce_reverse_tail_snoc {V : Type*} {H : SimpleGraph V} {l : ℕ}
    (hl : 2 ≤ l) {g : Fin (l + 1) → V} (hg : IsIndexedPath H g) (v : V)
    (hv : ∀ i : Fin (l + 1), 0 < i.val → g i ≠ v)
    (hadj : H.Adj (g ⟨1, by omega⟩) v) :
    ∃ h : Fin (l + 1) → V, IsIndexedPath H h ∧
      h 0 = g (Fin.last l) ∧ h (Fin.last l) = v ∧
      ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
        ∃ j : Fin (l + 1), 0 < j.val ∧ j.val < l ∧ h i = g j := by
  obtain ⟨s, rfl⟩ : ∃ s, l = s + 2 := ⟨l - 2, by omega⟩
  let f : Fin (s + 2) → V := fun i => g i.rev.succ
  have hf : IsIndexedPath H f := indexedPath_reverse (ce_indexedPath_tail hg)
  have hfv : v ∉ Set.range f := by
    rintro ⟨i, hi⟩
    exact hv i.rev.succ (by simp) hi
  have hfl : f (Fin.last (s + 1)) = g ⟨1, by omega⟩ := by
    simp [f]
  refine ⟨Fin.snoc f v, indexedPath_snoc hf hfv (hfl.symm ▸ hadj), ?_, ?_, ?_⟩
  · have hz : (0 : Fin (s + 3)) = (0 : Fin (s + 2)).castSucc := rfl
    rw [hz, Fin.snoc_castSucc]
    simp [f]
  · exact Fin.snoc_last _ _
  · intro i hi hil
    let k : Fin (s + 2) := ⟨i.val, hil⟩
    have hki : k.castSucc = i := Fin.ext rfl
    refine ⟨k.rev.succ, by simp, ?_, ?_⟩
    · simp only [Fin.val_succ, Fin.val_rev]
      dsimp [k]
      omega
    · rw [← hki, Fin.snoc_castSucc]

theorem ce_no_external_common_neighbor {V : Type*} {H : SimpleGraph V} {r : ℕ}
    (hr : 2 ≤ r) {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    (hmax : ∀ q, HasCycle H q → q ≤ r + 1) {x : V}
    (hx : ∀ i, c i ≠ x) (h0 : H.Adj (c 0) x) :
    ¬ H.Adj (c ⟨1, by omega⟩) x := by
  intro h1
  let one : Fin (r + 1) := ⟨1, by omega⟩
  have h01 : c 0 ≠ c one := by
    intro h
    have hv := congrArg Fin.val (hc h)
    simp only [Fin.val_zero, one] at hv
    omega
  let g : Fin 3 → V := ![c 0, x, c one]
  have hg : IsIndexedPath H g := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [g]
      exact False.elim (hx one rfl)
    · intro i
      fin_cases i
      · simpa [g] using h0
      · simpa [g] using h1.symm
  have hend : g (Fin.last 2) = c ((0 : Fin (r + 1)) + 1) := by
    have h : (1 : Fin (r + 1)) = one := by
      apply Fin.ext
      simp [one, Nat.mod_eq_of_lt (show 1 < r + 1 by omega)]
    simp [g, h]
  have hd : ∀ i : Fin 3, 0 < i.val → i.val < 2 →
      ∀ j : Fin (r + 1), c j ≠ g i := by
    intro i hi hi' j
    have heq : i = 1 := by apply Fin.ext; simp; omega
    simpa [heq, g] using hx j
  have h := hmax (r + 2) (ce_consecutive_ear_cycle (by omega) hc he 0 hg (by simp [g]) hend hd)
  omega

/-- In a graph with no independent triple, a longest cycle has no exterior ear
whose second endpoint is not the predecessor of the first. -/
theorem ce_nonwrapping_ear_impossible {V : Type*} {H : SimpleGraph V} {r l : ℕ}
    (hr : 2 ≤ r) (hl : 2 ≤ l) {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    (hmax : ∀ q, HasCycle H q → q ≤ r + 1) (hα : ¬ HasIndependent H 3)
    (j : Fin r) (hj : 0 < j.val) {g : Fin (l + 1) → V} (hg : IsIndexedPath H g)
    (hg0 : g 0 = c 0) (hgl : g (Fin.last l) = c j.castSucc)
    (hdis : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
      ∀ k : Fin (r + 1), c k ≠ g i) : False := by
  let one : Fin (r + 1) := ⟨1, by omega⟩
  let first : Fin (l + 1) := ⟨1, by omega⟩
  have hx : ∀ k, c k ≠ g first := hdis first (by simp [first]) (by dsimp [first]; omega)
  have h01x : H.Adj (c 0) (g first) := by
    simpa only [hg0] using (show H.Adj (g 0) (g first) from hg.2 ⟨0, by omega⟩)
  have h1x : ¬ H.Adj (c one) (g first) :=
    ce_no_external_common_neighbor hr hc he hmax hx h01x
  have hchord : ¬ H.Adj (c one) (c j.succ) := by
    intro h
    have hn := hmax (r + l) (ce_chord_ear_cycle hl hc he j hj h hg hg0 hgl hdis)
    omega
  have hdist : c one ≠ c j.succ := by
    intro h
    have hv := congrArg Fin.val (hc h)
    simp only [one, Fin.val_succ] at hv
    omega
  have hnextx : H.Adj (c j.succ) (g first) := by
    by_contra h
    exact hα (hasIndependent_three_of_distinct_nonadjacent hdist (hx one) (hx j.succ)
      hchord h1x h)
  have hjnext : cycleNext j.castSucc = j.succ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt j.succ.isLt
  have hbnext : c j.castSucc ≠ c j.succ := (hjnext ▸ he j.castSucc).ne
  have hv : ∀ i : Fin (l + 1), 0 < i.val → g i ≠ c j.succ := by
    intro i hi
    by_cases hil : i.val < l
    · exact (hdis i hi hil j.succ).symm
    · have hi' : i = Fin.last l := by apply Fin.ext; have := i.isLt; simp; omega
      simpa only [hi', hgl] using hbnext
  obtain ⟨p, hp, hp0, hpl, hpm⟩ := ce_reverse_tail_snoc hl hg (c j.succ) hv hnextx.symm
  have hend : p (Fin.last l) = c (j.castSucc + 1) := by
    rw [← cycleNext_eq_add_one, hjnext]
    exact hpl
  have hd : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
      ∀ k : Fin (r + 1), c k ≠ p i := by
    intro i hi hil k
    obtain ⟨u, hu, hul, hiu⟩ := hpm i hi hil
    rw [hiu]
    exact hdis u hu hul k
  have hn := hmax (r + l) (ce_consecutive_ear_cycle hl hc he j.castSucc hp
    (hp0.trans hgl) hend hd)
  omega

theorem ce_rooted_ear_impossible {V : Type*} {H : SimpleGraph V} {r l : ℕ}
    (hr : 2 ≤ r) (hl : 2 ≤ l) {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    (hmax : ∀ q, HasCycle H q → q ≤ r + 1) (hα : ¬ HasIndependent H 3)
    {g : Fin (l + 1) → V} (hg : IsIndexedPath H g)
    (hg0 : g 0 = c 0) (hgl : g (Fin.last l) ∈ Set.range c)
    (hdis : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
      ∀ k : Fin (r + 1), c k ≠ g i) : False := by
  obtain ⟨j, hj⟩ := hgl
  have hj0 : j ≠ 0 := by
    intro h
    have hv := congrArg Fin.val (hg.1 (hj.symm.trans (h ▸ hg0.symm)))
    simp only [Fin.val_last, Fin.val_zero] at hv
    omega
  by_cases hjlast : j = Fin.last r
  · have hp : IsIndexedPath H (g ∘ Fin.rev) := indexedPath_reverse hg
    have hp0 : (g ∘ Fin.rev) 0 = c (Fin.last r) := by
      simpa only [Function.comp_apply, Fin.rev_zero, hjlast] using hj.symm
    have hn : cycleNext (Fin.last r) = 0 := by
      apply Fin.ext
      simp [cycleNext]
    have hpl : (g ∘ Fin.rev) (Fin.last l) = c (Fin.last r + 1) := by
      rw [← cycleNext_eq_add_one, hn]
      simpa only [Function.comp_apply, Fin.rev_last] using hg0
    have hd : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
        ∀ k : Fin (r + 1), c k ≠ (g ∘ Fin.rev) i := by
      intro i hi hil k
      apply hdis i.rev (by simp only [Fin.val_rev]; omega) (by simp only [Fin.val_rev]; omega) k
    have h := hmax (r + l) (ce_consecutive_ear_cycle hl hc he (Fin.last r) hp hp0 hpl hd)
    omega
  · have hjlt : j.val < r := by
      have hneq : j.val ≠ r := fun h => hjlast (Fin.ext h)
      have := j.isLt
      omega
    let j' : Fin r := ⟨j.val, hjlt⟩
    have hcast : j'.castSucc = j := Fin.ext rfl
    have hjpos : 0 < j'.val := by
      have hneq : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      dsimp [j']
      omega
    exact ce_nonwrapping_ear_impossible hr hl hc he hmax hα j' hjpos hg hg0
      (by simpa only [hcast] using hj.symm) hdis

/-- A longest cycle in an alpha-two graph cannot have an exterior ear. -/
theorem ce_external_ear_impossible {V : Type*} {H : SimpleGraph V} {r l : ℕ}
    (hr : 2 ≤ r) (hl : 2 ≤ l) {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    (hmax : ∀ q, HasCycle H q → q ≤ r + 1) (hα : ¬ HasIndependent H 3)
    {g : Fin (l + 1) → V} (hg : IsIndexedPath H g)
    (hg0 : g 0 ∈ Set.range c) (hgl : g (Fin.last l) ∈ Set.range c)
    (hdis : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
      ∀ k : Fin (r + 1), c k ≠ g i) : False := by
  obtain ⟨a, ha⟩ := hg0
  let d : Fin (r + 1) → V := fun i => c (i + a)
  obtain ⟨hd, hde⟩ := ce_cycle_rotate hc he a
  have hd0 : g 0 = d 0 := by simpa only [d, zero_add] using ha.symm
  have hdlast : g (Fin.last l) ∈ Set.range d := by
    obtain ⟨b, hb⟩ := hgl
    exact ⟨b - a, by simpa only [d, sub_add_cancel] using hb⟩
  exact ce_rooted_ear_impossible hr hl hd hde hmax hα hg hd0 hdlast
    (fun i hi hil k => hdis i hi hil (k + a))

end CycleClique.Construction

end OAI
