import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Magnitudes
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.DictionaryPrefixes
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn

namespace OAI

/-!
# Exact fixed-width keys for weights and top masks

Weights use a sign bit followed by `2u` magnitude bits. Representation keys
append the entire indexed mask, using one bit per input index. Every key has
the same width, even on an outcome where its numerical value is not used.
The input magnitude bounds guarantee injectivity for all actual weights.
-/

namespace LowSpaceSubsetSum.WeightEncoding

def natBits (width value : ℕ) : List Bool :=
  List.ofFn (fun i : Fin width => value.testBit i.val)

@[simp] theorem natBits_length (width value : ℕ) : (natBits width value).length = width := by
  simp [natBits]

theorem natBits_injective {width x y : ℕ} (hx : x < 2 ^ width) (hy : y < 2 ^ width)
    (h : natBits width x = natBits width y) : x = y := by
  have he : (fun i : Fin width => x.testBit i.val) = fun i : Fin width => y.testBit i.val :=
    List.ofFn_injective h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < width
  · exact congrFun he ⟨i, hi⟩
  · have hw : width ≤ i := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hw
    rw [Nat.testBit_eq_false_of_lt (hx.trans_le hp),
      Nat.testBit_eq_false_of_lt (hy.trans_le hp)]

def signedBits (width : ℕ) (value : ℤ) : List Bool :=
  decide (value < 0) :: natBits width value.natAbs

@[simp] theorem signedBits_length (width : ℕ) (value : ℤ) :
    (signedBits width value).length = width + 1 := by simp [signedBits]

theorem signedBits_injective {width : ℕ} {x y : ℤ}
    (hx : x.natAbs < 2 ^ width) (hy : y.natAbs < 2 ^ width)
    (h : signedBits width x = signedBits width y) : x = y := by
  obtain ⟨hs, hm⟩ := List.cons.inj h
  have habs := natBits_injective hx hy hm
  have hsign : x < 0 ↔ y < 0 := decide_eq_decide.mp hs
  by_cases hn : x < 0
  · have hyn := hsign.mp hn
    calc
      x = -(x.natAbs : ℤ) := Int.eq_neg_natAbs_of_nonpos hn.le
      _ = -(y.natAbs : ℤ) := by rw [habs]
      _ = y := (Int.eq_neg_natAbs_of_nonpos hyn.le).symm
  · have hyn : ¬ y < 0 := fun h => hn (hsign.mpr h)
    calc
      x = (x.natAbs : ℤ) := Int.eq_natAbs_of_nonneg (by omega)
      _ = (y.natAbs : ℤ) := by rw [habs]
      _ = y := (Int.eq_natAbs_of_nonneg (by omega)).symm

def maskBits {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ S))

@[simp] theorem maskBits_length {n : ℕ} (S : Finset (Fin n)) :
    (maskBits S).length = n := by simp [maskBits]

theorem maskBits_injective {n : ℕ} : Function.Injective (@maskBits n) := by
  intro S T h
  have he : (fun i : Fin n => decide (i ∈ S)) = fun i : Fin n => decide (i ∈ T) :=
    List.ofFn_injective h
  apply Finset.ext
  intro i
  exact decide_eq_decide.mp (congrFun he i)

def weightWidth {n : ℕ} (I : Instance n) : ℕ := 2 * inputScale I + 1
def entryWidth {n : ℕ} (I : Instance n) : ℕ := weightWidth I + n

def weightKey {n : ℕ} (I : Instance n) (x : ℤ) : List Bool :=
  signedBits (2 * inputScale I) x

def entryKey {n : ℕ} (I : Instance n) (e : Entry (Fin n)) : List Bool :=
  weightKey I e.value ++ maskBits e.mask

@[simp] theorem weightKey_length {n : ℕ} (I : Instance n) (x : ℤ) :
    (weightKey I x).length = weightWidth I := by simp [weightKey, weightWidth]

@[simp] theorem entryKey_length {n : ℕ} (I : Instance n) (e : Entry (Fin n)) :
    (entryKey I e).length = entryWidth I := by simp [entryKey, entryWidth]

def BoundedWeight {n : ℕ} (I : Instance n) (x : ℤ) : Prop :=
  x.natAbs ≤ (2 * n + 1) * 2 ^ inputBits I

theorem boundedWeight_bits {n : ℕ} (I : Instance n) {x : ℤ} (hx : BoundedWeight I x) :
    x.natAbs < 2 ^ (2 * inputScale I) := by
  simpa only [sub_zero] using relevant_difference_bits I hx
    (show (0 : ℤ).natAbs ≤ (2 * n + 1) * 2 ^ inputBits I by simp)

theorem weightKey_injective {n : ℕ} (I : Instance n) {x y : ℤ}
    (hx : BoundedWeight I x) (hy : BoundedWeight I y)
    (h : weightKey I x = weightKey I y) : x = y :=
  signedBits_injective (boundedWeight_bits I hx) (boundedWeight_bits I hy) h

theorem weightKey_eq_iff {n : ℕ} (I : Instance n) {x y : ℤ}
    (hx : BoundedWeight I x) (hy : BoundedWeight I y) :
    weightKey I x = weightKey I y ↔ x = y :=
  ⟨weightKey_injective I hx hy, congrArg (weightKey I)⟩

theorem entryKey_injective {n : ℕ} (I : Instance n) {e f : Entry (Fin n)}
    (he : BoundedWeight I e.value) (hf : BoundedWeight I f.value)
    (h : entryKey I e = entryKey I f) : e = f := by
  have hw : (weightKey I e.value).length = (weightKey I f.value).length := by simp
  have hp := List.append_inj h hw
  have hv := weightKey_injective I he hf hp.1
  have hm := maskBits_injective hp.2
  cases e
  cases f
  simp_all

theorem signed_weight_bounded {n : ℕ} (I : Instance n) (F S : Finset (Fin n)) :
    BoundedWeight I (weight (flip (fun i => (I.values i : ℤ)) F) S) := by
  exact (signed_weight_natAbs_le I F S).trans (Nat.mul_le_mul_right _ (by omega))

theorem signed_target_bounded {n : ℕ} (I : Instance n) (F : Finset (Fin n)) :
    BoundedWeight I ((I.target : ℤ) - weight (fun i => (I.values i : ℤ)) F) := by
  exact (signed_target_natAbs_le I F).trans (Nat.mul_le_mul_right _ (by omega))

theorem raw_signed_weight_bounded {n : ℕ} (I : Instance n)
    (F : Finset (Fin n)) (xs : List (Fin n)) (hlen : xs.length ≤ 2 * n) :
    BoundedWeight I (occurrenceWeight (flip (fun i => (I.values i : ℤ)) F) xs) := by
  exact (raw_signed_weight_natAbs_le I F xs hlen).trans (Nat.mul_le_mul_right _ (by omega))

/-- The exact number of encoded bits is linear in the original input scale. -/
theorem widths_le {n : ℕ} (I : Instance n) :
    weightWidth I ≤ 2 * inputScale I + 1 ∧ entryWidth I ≤ 3 * inputScale I + 1 := by
  dsimp only [weightWidth, entryWidth, inputScale]
  omega

theorem weight_lookup_steps {n : ℕ} (I : Instance n) (t : BinaryTrie.Tree) (x : ℤ) :
    BinaryTrie.lookupSteps t (weightKey I x) ≤ 2 * inputScale I + 2 := by
  simpa only [weightKey_length, weightWidth, Nat.add_assoc] using
    BinaryTrie.lookupSteps_le t (weightKey I x)

theorem entry_lookup_steps {n : ℕ} (I : Instance n) (t : BinaryTrie.Tree)
    (e : Entry (Fin n)) :
    BinaryTrie.lookupSteps t (entryKey I e) ≤ 3 * inputScale I + 2 := by
  exact (BinaryTrie.lookupSteps_le t (entryKey I e)).trans (by
    rw [entryKey_length]
    have h := (widths_le I).2
    omega)

theorem entry_insert_nodes {n C : ℕ} (I : Instance n) {t : BinaryTrie.Tree}
    (ht : BinaryTrie.HasWidth t (entryWidth I)) (hc : BinaryTrie.Compact t)
    (hcap : BinaryTrie.entries t ≤ C) (e : Entry (Fin n)) :
    BinaryTrie.nodes (BinaryTrie.insert t (entryKey I e)) ≤
      (3 * inputScale I + 2) * (C + 1) := by
  apply (BinaryTrie.nodes_insert_le_capacity ht hc (entryKey_length I e) hcap).trans
  exact Nat.mul_le_mul_right _ (by have h := (widths_le I).2; omega)

end LowSpaceSubsetSum.WeightEncoding

end OAI
