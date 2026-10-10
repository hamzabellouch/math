import OAI.GroupTheory.PolycyclicRecognition.Algebra.DerivationEigenvectors
import Mathlib.Data.List.OfFn

namespace OAI

/-! # Word-length filtration for a nilpotent generated algebra

Left multiplication raises word length; a derivation carrying generators to
generators preserves it. This separates the nilpotent and semisimple parts
of the finite solvable representation.
-/

noncomputable section
namespace PolycyclicRecognition

variable {A ι : Type*} [Ring A] [Algebra ℝ A] (j : ι → A)

def wordLengthSpan (k : ℕ) : Submodule ℝ A :=
  Submodule.span ℝ {a | ∃ l : List ι, k ≤ l.length ∧ (l.map j).prod = a}

theorem wordLengthSpan_antitone : Antitone (wordLengthSpan j) := by
  intro k l hkl
  apply Submodule.span_mono
  rintro a ⟨w, hw, rfl⟩
  exact ⟨w, hkl.trans hw, rfl⟩

theorem wordLengthSpan_generator_mul (k : ℕ) (x : ι) {a : A}
    (ha : a ∈ wordLengthSpan j k) : j x * a ∈ wordLengthSpan j (k + 1) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    apply Submodule.subset_span
    exact ⟨x :: l, Nat.succ_le_succ hl, by simp⟩
  | zero => simpa only [mul_zero] using (wordLengthSpan j (k + 1)).zero_mem
  | add a b _ _ ha hb =>
    rw [mul_add]
    exact (wordLengthSpan j (k + 1)).add_mem ha hb
  | smul r a _ ha =>
    rw [Algebra.mul_smul_comm]
    exact (wordLengthSpan j (k + 1)).smul_mem r ha

theorem wordLengthSpan_zero_eq_top (hgen : Algebra.adjoin ℝ (Set.range j) = ⊤) :
    wordLengthSpan j 0 = ⊤ := by
  have hle : (Algebra.adjoin ℝ (Set.range j)).toSubmodule ≤ wordLengthSpan j 0 := by
    rw [Algebra.adjoin_eq_span]
    apply Submodule.span_le.mpr
    intro a ha
    have hw : ∃ l : List ι, (l.map j).prod = a := by
      induction ha using Submonoid.closure_induction with
      | mem a ha =>
        obtain ⟨x, rfl⟩ := ha
        exact ⟨[x], by simp⟩
      | one => exact ⟨[], by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨v, rfl⟩ := ha
        obtain ⟨w, rfl⟩ := hb
        exact ⟨v ++ w, by simp⟩
    obtain ⟨l, rfl⟩ := hw
    exact Submodule.subset_span ⟨l, Nat.zero_le _, rfl⟩
  apply top_unique
  rw [hgen] at hle
  exact hle

theorem wordLengthSpan_eq_bot (c : ℕ)
    (hnil : ∀ l : List ι, c ≤ l.length → (l.map j).prod = 0) :
    wordLengthSpan j c = ⊥ := by
  apply eq_bot_iff.mpr
  apply Submodule.span_le.mpr
  rintro a ⟨l, hl, rfl⟩
  exact (Submodule.mem_bot ℝ).mpr (hnil l hl)

variable (D : Module.End ℝ A) (f : ι → ι)
  (hmul : ∀ a b, D (a * b) = a * D b + D a * b)
  (hone : D 1 = 0) (hgen : ∀ x, D (j x) = j (f x))

include f hmul hone hgen

theorem wordLengthSpan_prefix_derivative (k : ℕ) (p l : List ι)
    (h : k ≤ p.length + l.length) :
    (p.map j).prod * D (l.map j).prod ∈ wordLengthSpan j k := by
  induction l generalizing p with
  | nil =>
    simpa only [List.map_nil, List.prod_nil, hone, mul_zero] using (wordLengthSpan j k).zero_mem
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, hmul, hgen, mul_add]
    apply (wordLengthSpan j k).add_mem
    · have hp : k ≤ (p ++ [x]).length + l.length := by
        simpa only [List.length_append, List.length_singleton, List.length_cons,
          List.length_nil, zero_add, Nat.add_assoc, Nat.add_comm 1] using h
      simpa only [List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, mul_assoc] using ih (p ++ [x]) hp
    · apply Submodule.subset_span
      refine ⟨p ++ f x :: l, ?_, ?_⟩
      · simpa only [List.length_append, List.length_cons] using h
      · simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons]

theorem wordLengthSpan_derivative (k : ℕ) {a : A} (ha : a ∈ wordLengthSpan j k) :
    D a ∈ wordLengthSpan j k := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    simpa only [List.map_nil, List.prod_nil, one_mul] using
      wordLengthSpan_prefix_derivative j D f hmul hone hgen k [] l (by simpa using hl)
  | zero => simpa only [map_zero] using (wordLengthSpan j k).zero_mem
  | add a b _ _ ha hb =>
    rw [map_add]
    exact (wordLengthSpan j k).add_mem ha hb
  | smul r a _ ha =>
    rw [map_smul]
    exact (wordLengthSpan j k).smul_mem r ha

end PolycyclicRecognition

end

end OAI
