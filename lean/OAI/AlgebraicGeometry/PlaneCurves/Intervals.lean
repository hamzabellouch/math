import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Counting integers in open intervals; Integral residue classes of theta exponents
-/

section

/-! Integer interval counting used in Lemma `integer-rows`, section 04.
The finite set contains distinct integers by construction; real endpoints and
singleton intervals are allowed. -/
namespace Nagata.W02

/-- A nonempty finite set of integers occupies at least `card - 1` units. -/
theorem card_le_max_sub_min_add_one (s : Finset ℤ) (hs : s.Nonempty) :
    (s.card : ℤ) ≤ s.max' hs - s.min' hs + 1 := by
  have hsub : s ⊆ Finset.Icc (s.min' hs) (s.max' hs) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨s.min'_le x hx, s.le_max' x hx⟩
  have hc := Finset.card_le_card hsub
  have hm := s.min'_le_max' hs
  have hi := Int.card_Icc_of_le (s.min' hs) (s.max' hs) (show s.min' hs ≤ s.max' hs + 1 by omega)
  have hcast : (s.card : ℤ) ≤ (Finset.card (Finset.Icc (s.min' hs) (s.max' hs)) : ℤ) := by
    exact_mod_cast hc
  omega

/-- A finite set of integers in a nonempty real interval has cardinality at
most the interval length plus one. No alignment assumption is needed. -/
theorem card_le_interval_length_add_one (s : Finset ℤ) (a b : ℝ)
    (hab : a ≤ b) (h : ∀ k ∈ s, a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b) :
    (s.card : ℝ) ≤ b - a + 1 := by
  by_cases hs : s.Nonempty
  · have hc := card_le_max_sub_min_add_one s hs
    have hcR : (s.card : ℝ) ≤ (s.max' hs : ℝ) - (s.min' hs : ℝ) + 1 := by
      exact_mod_cast hc
    have hmin := (h _ (s.min'_mem hs)).1
    have hmax := (h _ (s.max'_mem hs)).2
    linarith
  · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hz, Finset.card_empty, Nat.cast_zero]
    linarith

/-- If the interval length is strictly less than an integer `m`, at most `m`
integer positions can occur. This includes empty and singleton rows. -/
theorem card_le_of_interval_length_lt (s : Finset ℤ) (a b : ℝ) (m : ℕ)
    (hab : a ≤ b) (h : ∀ k ∈ s, a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b)
    (hlen : b - a < (m : ℝ)) : s.card ≤ m := by
  have hc := card_le_interval_length_add_one s a b hab h
  have hh : (s.card : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hn : s.card < m + 1 := by exact_mod_cast hh
  omega

/-- At least `t` integer positions force interval length at least `t - 1`. -/
theorem sub_one_le_interval_length (s : Finset ℤ) (a b : ℝ) (t : ℕ)
    (hab : a ≤ b) (h : ∀ k ∈ s, a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b)
    (ht : t ≤ s.card) : (t : ℝ) - 1 ≤ b - a := by
  have hc := card_le_interval_length_add_one s a b hab h
  have htR : (t : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast ht
  linarith

/-- The translation-independent bound with the spare endpoint absorbed by a
unit margin, as in the height count of Lemma `integer-rows`. -/
theorem card_le_of_interval_length_add_one_le (s : Finset ℤ) (a b : ℝ) (M : ℕ)
    (hab : a ≤ b) (h : ∀ k ∈ s, a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b)
    (hlen : b - a + 1 ≤ (M : ℝ)) : s.card ≤ M := by
  have hc := (card_le_interval_length_add_one s a b hab h).trans hlen
  exact_mod_cast hc

/-- Open endpoints permit a non-strict bound on the interval length. -/
theorem card_le_of_open_interval_length_le (s : Finset ℤ) (a b : ℝ) (m : ℕ)
    (h : ∀ k ∈ s, a < (k : ℝ) ∧ (k : ℝ) < b)
    (hlen : b - a ≤ (m : ℝ)) : s.card ≤ m := by
  by_cases hs : s.Nonempty
  · have hc := card_le_max_sub_min_add_one s hs
    have hcR : (s.card : ℝ) ≤ (s.max' hs : ℝ) - (s.min' hs : ℝ) + 1 := by
      exact_mod_cast hc
    have hmin := (h _ (s.min'_mem hs)).1
    have hmax := (h _ (s.max'_mem hs)).2
    have hh : (s.card : ℝ) < ((m + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hn : s.card < m + 1 := by exact_mod_cast hh
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

end Nagata.W02

end

section

/-!
# The integer indexing of normalized theta sections
-/

namespace Nagata.W09

/-- The consecutive integers used to index a theta basis. -/
noncomputable def thetaIndices (U : ℝ) (n : ℤ) : Finset ℤ :=
  Finset.Ioc ⌊U⌋ (⌊U⌋ + n)

/-- For a nonintegral left endpoint, these are exactly the integers in `(U,U+n)`. -/
theorem mem_thetaIndices_iff {U : ℝ} {n K : ℤ}
    (hU : U ∉ Set.range (Int.cast : ℤ → ℝ)) :
    K ∈ thetaIndices U n ↔ U < (K : ℝ) ∧ (K : ℝ) < U + (n : ℝ) := by
  rw [thetaIndices, Finset.mem_Ioc]
  constructor
  · rintro ⟨hK, hKn⟩
    refine ⟨Int.floor_lt.mp hK, ?_⟩
    have hfloor : (⌊U⌋ : ℝ) < U := Int.floor_lt_self_iff.mpr hU
    have hcast : (K : ℝ) ≤ (⌊U⌋ : ℝ) + (n : ℝ) := by
      simpa only [Int.cast_add] using
        (show (K : ℝ) ≤ ((⌊U⌋ + n : ℤ) : ℝ) from Int.cast_le.mpr hKn)
    linarith
  · rintro ⟨hK, hKn⟩
    refine ⟨Int.floor_lt.mpr hK, ?_⟩
    have hle : K ≤ ⌊U + (n : ℝ)⌋ := Int.le_floor.mpr hKn.le
    simpa only [Int.floor_add_intCast] using hle

/-- An interval with integral positive length has that many integer indices. -/
theorem card_thetaIndices (U : ℝ) (n : ℤ) :
    (thetaIndices U n).card = n.toNat := by
  simp only [thetaIndices, Int.card_Ioc, add_sub_cancel_left]

end Nagata.W09

end

section

namespace Nagata.W09

/-- Modulo the interval length, two of the chosen consecutive integers cannot agree. -/
theorem thetaIndices_residue_injective {U : ℝ} {n a b : ℤ}
    (ha : a ∈ thetaIndices U n) (hb : b ∈ thetaIndices U n)
    (hab : a % n = b % n) : a = b := by
  simp only [thetaIndices, Finset.mem_Ioc] at ha hb
  have ha0 : 0 ≤ a - (⌊U⌋ + 1) := by omega
  have han : a - (⌊U⌋ + 1) < n := by omega
  have hb0 : 0 ≤ b - (⌊U⌋ + 1) := by omega
  have hbn : b - (⌊U⌋ + 1) < n := by omega
  have h : (a - (⌊U⌋ + 1)) % n = (b - (⌊U⌋ + 1)) % n := by
    conv_lhs => rw [Int.sub_emod]
    conv_rhs => rw [Int.sub_emod]
    rw [hab]
  rw [Int.emod_eq_of_lt ha0 han, Int.emod_eq_of_lt hb0 hbn] at h
  omega

/-- Every integer residue is represented by one of the chosen indices. -/
theorem exists_thetaIndex_modEq (U : ℝ) {n : ℤ} (hn : 0 < n) (z : ℤ) :
    ∃ K ∈ thetaIndices U n, K % n = z % n := by
  let a := ⌊U⌋ + 1
  refine ⟨a + (z - a) % n, ?_, ?_⟩
  · simp only [thetaIndices, Finset.mem_Ioc]
    have h0 := Int.emod_nonneg (z - a) (ne_of_gt hn)
    have hlt := Int.emod_lt_of_pos (z - a) hn
    dsimp [a] at *
    omega
  · have h : (a + (z - a) % n) % n = (a + (z - a)) % n := by
      simp only [Int.add_emod, Int.emod_emod]
    have hz : a + (z - a) = z := by omega
    rw [hz] at h
    exact h

/-- Exactly one index represents each residue class; no analytic hypotheses are used. -/
theorem existsUnique_thetaIndex_modEq (U : ℝ) {n : ℤ} (hn : 0 < n) (z : ℤ) :
    ∃! K : ℤ, K ∈ thetaIndices U n ∧ K % n = z % n := by
  obtain ⟨K, hK, hKz⟩ := exists_thetaIndex_modEq U hn z
  refine ⟨K, ⟨hK, hKz⟩, ?_⟩
  rintro L ⟨hL, hLz⟩
  exact thetaIndices_residue_injective hL hK (hLz.trans hKz.symm)

/-- Source-form statement of existence and uniqueness in the open real interval. -/
theorem existsUnique_integer_in_open_interval_modEq {U : ℝ} {n : ℤ}
    (hn : 0 < n) (hU : U ∉ Set.range (Int.cast : ℤ → ℝ)) (z : ℤ) :
    ∃! K : ℤ, (U < (K : ℝ) ∧ (K : ℝ) < U + (n : ℝ)) ∧ K % n = z % n := by
  simpa only [mem_thetaIndices_iff hU] using existsUnique_thetaIndex_modEq U hn z

end Nagata.W09

end

end OAI
