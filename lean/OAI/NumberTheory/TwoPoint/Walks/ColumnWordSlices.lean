import OAI.NumberTheory.TwoPoint.Walks.ColumnBlockGeometry

namespace OAI

/-! Actual contiguous column blocks retain their signed word and coefficient geometry. -/

namespace TwoPointCorrelations.ColumnWordPattern

open Finset

variable {α : Type*}

def slice (w : ColumnWordPattern α) (start len : ℕ) : ColumnWordPattern α where
  length := len
  label := fun t => w.label (start + t)
  forward := fun t => w.forward (start + t)
  padding := fun t => w.padding (start + t)
  otherColumns := fun t => w.otherColumns (start + t)

theorem slice_word (w : ColumnWordPattern α) (value : α → ℕ) (start len : ℕ)
    (h : start + len ≤ w.length) :
    (w.slice start len).word value = wordSlice (w.word value) start (start + len) := by
  apply List.ext_getElem
  · rw [word_length, wordSlice_length _ (by omega) (by simpa using h)]
    simp only [slice, Nat.add_sub_cancel_left]
  · intro i hi hj
    simp only [word, List.getElem_ofFn, wordSlice, List.getElem_take, List.getElem_drop,
      slice, step]

theorem slice_coefficient (w : ColumnWordPattern α) (h start len t : ℕ) :
    (w.slice start len).coefficient h t = w.coefficient h (start + t) := rfl

/-- Use positivity only on the actual perfect block; other positions in
the full trace word may be unlit. All global admissibility properties are
restricted to that block, and every scalar sum uses its original indices. -/
theorem block_geometry_of_slice (w : ColumnWordPattern α) (value : α → ℕ)
    (hvalue : Function.Injective value) (hprime : ∀ z, (value z).Prime)
    (hother : ∀ z t, t < w.length → ¬value z ∣ w.otherColumns t)
    {h s J : ℕ} {supply : ℕ → ℕ → Prop} {x : ℤ} (start len : ℕ)
    (hend : start + len ≤ w.length) (hshort : len ≤ s)
    (hw : PositiveWord h x (wordSlice (w.word value) start (start + len))) (hh : 0 < h)
    (heligible : ∀ a ∈ w.word value, supply a.tuple a.padding)
    (hq : ∀ a ∈ w.word value, 0 < a.padding)
    (hsq : ∀ a ∈ w.word value, Squarefree a.tuple)
    (hcard : ∀ a ∈ w.word value, a.tuple.primeFactors.card = J)
    (hchain : (wordSlice (w.word value) start (start + len)).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt (w.word value) p j →
      ¬p ∣ h ∧ ∀ a ∈ w.word value, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x (wordSlice (w.word value) start (start + len)) y →
      ¬ProhibitedSite h s supply y) :
    (∀ i j k : Fin len, i ≤ j → j ≤ k →
      w.label (start + i) = w.label (start + k) → w.label (start + j) = w.label (start + i)) ∧
    (∀ a b z, start ≤ a → a < b → b ≤ start + len →
      (∀ t ∈ Ico a b, w.label t = z) → (∑ t ∈ Ico a b, (w.coefficient h t : ℝ)) ≠ 0) := by
  let u := w.slice start len
  have he : u.word value = wordSlice (w.word value) start (start + len) := w.slice_word value start len hend
  have hsub := (wordSlice_infix (w.word value) start (start + len)).subset
  have hg := u.positive_block_geometry value hvalue hprime
    (fun z t ht => hother z (start + t) (by change t < len at ht; omega))
    (by simpa only [he] using hw) hh hshort
    (fun a ha => heligible a (hsub (he ▸ ha)))
    (fun a ha => hq a (hsub (he ▸ ha)))
    (fun a ha => hsq a (hsub (he ▸ ha)))
    (fun a ha => hcard a (hsub (he ▸ ha)))
    (by rw [he]; exact hchain)
    (by
      intro p j hp
      have hj : j < len := by simpa only [word_length, u, slice] using hp.index_lt
      have hp' : TuplePrimeAt (w.word value) p (start + j) := by
        apply (tuplePrimeAt_slice _ start (start + len) p j (by omega)).mp
        rwa [he] at hp
      have hd := hsupport p (start + j) hp'
      exact ⟨hd.1, fun a ha => hd.2 a (hsub (he ▸ ha))⟩)
    (by simpa only [he] using hsurvive)
  refine ⟨hg.1, ?_⟩
  intro a b z ha hab hb hc
  have hn := hg.2 (a - start) (b - start) z (by omega) (by change b - start ≤ len; omega) (by
    intro t ht
    apply hc
    obtain ⟨hl, hu⟩ := mem_Ico.mp ht
    exact mem_Ico.mpr ⟨by omega, by omega⟩)
  have heq := sum_Ico_add (fun t => (w.coefficient h t : ℝ)) (a - start) (b - start) start
  rw [Nat.sub_add_cancel ha, Nat.sub_add_cancel (by omega : start ≤ b)] at heq
  simpa only [u, slice_coefficient, heq] using hn

end TwoPointCorrelations.ColumnWordPattern

end OAI
