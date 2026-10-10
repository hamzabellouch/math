import OAI.NumberTheory.TwoPoint.Walks.ColumnWordSlices
import OAI.NumberTheory.TwoPoint.Bounds.LowRankColumnEncoding

namespace OAI

/-! Perfect blocks use only the lit divisibilities at their actual positions. -/

namespace TwoPointCorrelations

open Finset

theorem positiveWord_iff_departures (h : ℕ) (x : ℤ) (w : List SignedStep) :
    PositiveWord h x w ↔ ∀ i : Fin w.length,
      (w.get i).divisor ∣ x + wordDisplacement h (w.take i.val) := by
  induction w generalizing x with
  | nil => simp
  | cons a w ih =>
      rw [positiveWord_cons, ih]
      constructor
      · rintro ⟨ha, hw⟩ i
        rcases i with ⟨i, hi⟩
        cases i with
        | zero => simpa using ha
        | succ i =>
            simpa only [List.get_eq_getElem, List.getElem_cons_succ, List.take_succ_cons,
              wordDisplacement_cons, add_assoc] using hw ⟨i, by simpa using hi⟩
      · intro hw
        refine ⟨?_, ?_⟩
        · simpa using hw ⟨0, by simp⟩
        · intro i
          simpa only [List.get_eq_getElem, List.getElem_cons_succ, List.take_succ_cons,
            wordDisplacement_cons, add_assoc] using hw ⟨i.val + 1, by simp⟩

theorem positiveWord_slice_of_lit {h : ℕ} {x : ℤ} {w : List SignedStep}
    (start len : ℕ) (hend : start + len ≤ w.length)
    (hlit : ∀ i : Fin w.length, start ≤ i.val → i.val < start + len →
      (w.get i).divisor ∣ x + wordDisplacement h (w.take i.val)) :
    PositiveWord h (x + wordDisplacement h (w.take start)) (wordSlice w start (start + len)) := by
  rw [positiveWord_iff_departures]
  intro i
  have hi : i.val < len := by
    have hl : (wordSlice w start (start + len)).length = len := by
      rw [wordSlice_length w (a := start) (b := start + len) (by omega) hend, Nat.add_sub_cancel_left]
    exact i.isLt.trans_eq hl
  have hp := hlit ⟨start + i.val, by omega⟩
    (show start ≤ start + i.val by omega) (show start + i.val < start + len by omega)
  have htake : (wordSlice w start (start + len)).take i.val = wordSlice w start (start + i.val) := by
    simp only [wordSlice, List.take_take, Nat.add_sub_cancel_left, Nat.min_eq_left hi.le]
  have he := congrArg (wordDisplacement h) (wordSlice_split w (show start ≤ start + i.val by omega))
  rw [wordDisplacement_append] at he
  change ((wordSlice w start (start + len))[i.val]).divisor ∣ _
  rw [htake]
  simpa only [List.get_eq_getElem, wordSlice, List.getElem_take, List.getElem_drop,
    ← he, add_assoc] using hp

theorem wordVertex_slice {h : ℕ} {x y : ℤ} {w : List SignedStep}
    (start len : ℕ)
    (hy : WordVertex h (x + wordDisplacement h (w.take start))
      (wordSlice w start (start + len)) y) : WordVertex h x w y := by
  obtain ⟨a, b, hab, hy⟩ := hy
  refine ⟨w.take start ++ a, b ++ w.drop (start + len), ?_, ?_⟩
  · calc
      w = w.take (start + len) ++ w.drop (start + len) := (List.take_append_drop _ _).symm
      _ = (w.take start ++ wordSlice w start (start + len)) ++ w.drop (start + len) := by
        rw [wordSlice_split w (by omega)]
      _ = (w.take start ++ a) ++ (b ++ w.drop (start + len)) := by
        rw [hab]
        simp only [List.append_assoc]
  · rw [wordDisplacement_append]
    simpa only [add_assoc] using hy

namespace ColumnWordPattern

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- Every numerical perfect block has the geometric properties used by
the universal code. Positivity is assumed only at the perfect positions;
unlit positions elsewhere in the trace impose no condition here. -/
theorem short_geometry_of_lit (w : ColumnWordPattern α) (hn : 0 < w.length)
    (value : α → ℕ) (hvalue : Function.Injective value) (hprime : ∀ z, (value z).Prime)
    (hother : ∀ z t, t < w.length → ¬value z ∣ w.otherColumns t)
    {h s J : ℕ} {supply : ℕ → ℕ → Prop} {x : ℤ} (hh : 0 < h)
    (perfect : Finset (Fin w.length))
    (hlit : ∀ i ∈ perfect, (w.step value i.val).divisor ∣
      x + wordDisplacement h ((w.word value).take i.val))
    (heligible : ∀ a ∈ w.word value, supply a.tuple a.padding)
    (hq : ∀ a ∈ w.word value, 0 < a.padding)
    (hsq : ∀ a ∈ w.word value, Squarefree a.tuple)
    (hcard : ∀ a ∈ w.word value, a.tuple.primeFactors.card = J)
    (hchain : ∀ start len, start + len ≤ w.length → len ≤ s →
      (∀ t ∈ intervalPositions (start, len), columnNatPerfect perfect t = true) →
      (wordSlice (w.word value) start (start + len)).IsChain (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt (w.word value) p j →
      ¬p ∣ h ∧ ∀ a ∈ w.word value, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x (w.word value) y → ¬ProhibitedSite h s supply y) :
    ShortColumnGeometry (fun i : Fin w.length => w.label i.val) hn
      (fun t => (w.coefficient h t : ℝ)) perfect s := by
  intro start len hend hlen hperfect
  have hlabel (t : ℕ) (ht : t < w.length) :
      columnNatLabel (fun i : Fin w.length => w.label i.val) hn t = w.label t := by
    simp only [columnNatLabel, dite_eq_left ht]
  have hpositive := positiveWord_slice_of_lit (h := h) (x := x) (w := w.word value)
    start len (by simpa using hend) (by
      intro i hlo hhi
      have hit : i.val < w.length := by simpa only [word_length] using i.isLt
      have hp := hperfect i.val (by
        simp only [intervalPositions, List.mem_map, List.mem_range]
        exact ⟨i.val - start, by omega, by omega⟩)
      have him : (⟨i.val, hit⟩ : Fin w.length) ∈ perfect := by
        simpa only [columnNatPerfect, dite_eq_left hit, decide_eq_true_eq] using hp
      change ((w.word value)[i.val]).divisor ∣ _
      simpa only [word, List.getElem_ofFn] using hlit ⟨i.val, hit⟩ him)
  have hg := w.block_geometry_of_slice value hvalue hprime hother start len hend hlen
    hpositive hh heligible hq hsq hcard (hchain start len hend hlen hperfect) hsupport
    (fun y hy => hsurvive y (wordVertex_slice start len hy))
  constructor
  · intro i j k hij hjk he
    have hi : i.val < len := by simpa only [blockLabelList, List.length_map, List.length_range] using i.isLt
    have hj : j.val < len := by simpa only [blockLabelList, List.length_map, List.length_range] using j.isLt
    have hk : k.val < len := by simpa only [blockLabelList, List.length_map, List.length_range] using k.isLt
    have hget (q : Fin (blockLabelList (columnNatLabel (fun i : Fin w.length => w.label i.val) hn) start len).length)
        (hq : q.val < len) :
        (blockLabelList (columnNatLabel (fun i : Fin w.length => w.label i.val) hn) start len).get q =
          w.label (start + q.val) := by
      change (blockLabelList (columnNatLabel (fun i : Fin w.length => w.label i.val) hn) start len)[q.val] = _
      simp only [blockLabelList, List.getElem_map, List.getElem_range]
      exact hlabel _ (by omega)
    rw [hget i hi, hget k hk] at he
    rw [hget j hj, hget i hi]
    exact hg.1 ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk he
  · intro a b z ha hab hb hc
    apply hg.2 a b z ha hab hb
    intro t ht
    rw [← hlabel t (by have := (mem_Ico.mp ht).2; omega)]
    exact hc t ht

end ColumnWordPattern

end TwoPointCorrelations

end OAI
