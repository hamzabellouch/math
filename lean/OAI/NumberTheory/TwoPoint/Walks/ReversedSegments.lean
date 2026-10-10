import OAI.NumberTheory.TwoPoint.Walks.WordBlockGeometry

namespace OAI

/-! Reversed prohibited subwords used in the active-label descent. -/

namespace TwoPointCorrelations

lemma tuplePrimeAt_reverseWord (w : List SignedStep) (p i : ℕ) (hi : i < w.length) :
    TuplePrimeAt (reverseWord w) p i ↔ TuplePrimeAt w p (w.length - 1 - i) := by
  rw [tuplePrimeAt_iff_getElem _ _ _ (by simpa using hi),
    tuplePrimeAt_iff_getElem _ _ _ (by omega)]
  simp [reverseWord, SignedStep.flip]

lemma TuplePrimeIntervals.slice {w : List SignedStep} (hw : TuplePrimeIntervals w)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ w.length) : TuplePrimeIntervals (wordSlice w a b) := by
  have hlen := wordSlice_length w hab hb
  intro p i j k hij hjk hk hpi hpk
  have hi : i < b - a := by omega
  have hj : j < b - a := by omega
  have hk' : k < b - a := by omega
  apply (tuplePrimeAt_slice w a b p j hj).mpr
  exact hw p (a + i) (a + j) (a + k) (by omega) (by omega) (by omega)
    ((tuplePrimeAt_slice w a b p i hi).mp hpi)
    ((tuplePrimeAt_slice w a b p k hk').mp hpk)

lemma TuplePrimeIntervals.reverse {w : List SignedStep} (hw : TuplePrimeIntervals w) :
    TuplePrimeIntervals (reverseWord w) := by
  intro p i j k hij hjk hk hpi hpk
  have hk' : k < w.length := by simpa using hk
  rw [tuplePrimeAt_reverseWord w p j (by omega)]
  exact hw p (w.length - 1 - k) (w.length - 1 - j) (w.length - 1 - i)
    (by omega) (by omega) (by omega)
    ((tuplePrimeAt_reverseWord w p k hk').mp hpk)
    ((tuplePrimeAt_reverseWord w p i (by omega)).mp hpi)

lemma reverseWord_drop (w : List SignedStep) (i : ℕ) :
    (reverseWord w).drop i = reverseWord (w.take (w.length - i)) := by
  simp [reverseWord, List.drop_reverse]

lemma reverseWord_slice_drop (w : List SignedStep) {a b c : ℕ}
    (hac : a ≤ c) (hcb : c ≤ b) (hb : b ≤ w.length) :
    (reverseWord (wordSlice w a b)).drop (b - c) = reverseWord (wordSlice w a c) := by
  rw [reverseWord_drop, wordSlice_length w (by omega) hb]
  rw [show b - a - (b - c) = c - a by omega]
  congr 1
  simp only [wordSlice, List.take_take, Nat.min_eq_left (by omega : c - a ≤ b - a)]

lemma reverseWord_chain {w : List SignedStep}
    (hw : w.IsChain (fun a b => a.tuple ≠ b.tuple)) :
    (reverseWord w).IsChain (fun a b => a.tuple ≠ b.tuple) := by
  rw [List.isChain_iff_getElem] at hw ⊢
  intro i hi
  have hi' : i + 1 < w.length := by simpa using hi
  have h := hw (w.length - 2 - i) (by omega)
  have heq : w.length - 2 - i + 1 = w.length - 1 - i := by omega
  simp only [reverseWord, List.getElem_map, List.getElem_reverse,
    SignedStep.flip] at *
  simpa only [heq, show w.length - 1 - (i + 1) = w.length - 2 - i by omega] using h.symm

/-- The reversed interval is genuinely forward-prohibited. The divisible
suffix has length `c-a`, while its preceding part has positive length. -/
lemma reversed_interval_forwardProhibited (h s : ℕ) (supply : ℕ → ℕ → Prop)
    (w : List SignedStep) (hlen : w.length ≤ s)
    (hsupply : ∀ t ∈ w, supply t.tuple t.padding)
    (hchain : w.IsChain (fun a b => a.tuple ≠ b.tuple))
    (hinterval : TuplePrimeIntervals w) {a b c p : ℕ}
    (hac : a + 1 < c) (hcb : c < b) (hb : b ≤ w.length)
    (hp : TuplePrimeAt w p (b - 1)) (hnot : ¬TuplePrimeAt w p a)
    (hdiv : (p : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) a c) :
    ForwardProhibited h s supply (reverseWord (wordSlice w a b)) := by
  have hab : a ≤ b := by omega
  have hlength := wordSlice_length w hab hb
  refine ⟨by simp only [reverseWord_length, hlength]; omega,
    by simp only [reverseWord_length, hlength]; omega, ?_,
    reverseWord_chain ((hchain.drop a).take (b - a)),
    (hinterval.slice hab hb).reverse, p, ?_, ?_, b - c, by omega, ?_, ?_⟩
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    have hum : u ∈ wordSlice w a b := by simpa using hu
    exact hsupply u ((wordSlice_infix w a b).subset hum)
  · rw [tuplePrimeAt_reverseWord _ _ _ (by omega)]
    apply (tuplePrimeAt_slice w a b p _ (by omega)).mpr
    simpa only [show a + ((wordSlice w a b).length - 1 - 0) = b - 1 by omega] using hp
  · intro hp'
    rw [tuplePrimeAt_reverseWord _ _ _ (by simp only [reverseWord_length] at *; omega)] at hp'
    have hp'' := (tuplePrimeAt_slice w a b p _ (by omega)).mp hp'
    exact hnot (by simpa only [reverseWord_length,
      show a + ((wordSlice w a b).length - 1 - ((wordSlice w a b).length - 1)) = a by omega] using hp'')
  · simp only [reverseWord_length, hlength]
    omega
  · rw [reverseWord_slice_drop w (by omega) (by omega) hb,
      wordDisplacement_reverseWord, wordSlice_displacement h w (by omega)]
    exact hdiv.neg_right

end TwoPointCorrelations

end OAI
