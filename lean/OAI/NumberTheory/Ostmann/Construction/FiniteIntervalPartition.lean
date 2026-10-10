import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import OAI.NumberTheory.Ostmann.ZeroDensity.IntegerProgressionPartition

namespace OAI

/-! # Turning convex finite fibers into exact integer interval pieces -/

namespace Ostmann

open scoped Classical

/-- A finite set of consecutive natural numbers is an interval whose length
is exactly its cardinality, including the empty case. -/
theorem finite_convex_set_interval (s : Finset ℕ)
    (hc : ∀ x ∈ s, ∀ y ∈ s, ∀ z, x ≤ z → z ≤ y → z ∈ s) :
    ∃ a : ℕ, s = Finset.Ico a (a + s.card) := by
  by_cases hs : s.Nonempty
  · have he : s = Finset.Icc (s.min' hs) (s.max' hs) := by
      ext z
      constructor
      · intro hz
        exact Finset.mem_Icc.mpr ⟨s.min'_le z hz, s.le_max' z hz⟩
      · intro hz
        obtain ⟨hx, hy⟩ := Finset.mem_Icc.mp hz
        exact hc _ (s.min'_mem hs) _ (s.max'_mem hs) z hx hy
    have hcard : s.card = s.max' hs + 1 - s.min' hs := by
      conv_lhs => rw [he]
      exact Nat.card_Icc _ _
    refine ⟨s.min' hs, ?_⟩
    ext z
    conv_lhs => rw [he]
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    have hmm := s.min'_le_max' hs
    omega
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    exact ⟨0, by simp [he]⟩

/-- The fibers of a code on an integer interval become consecutive subintervals.
This provides the exact bijection needed by the character-sum partition. -/
theorem exists_finite_interval_partition {I : Type*} (N : ℕ) (code : ℕ → I)
    (hc : ∀ x y z, x < N → y < N → x ≤ z → z ≤ y →
      code x = code y → code z = code x) :
    ∃ (a K : I → ℕ) (e : Fin N ≃ Σ i, Fin (K i)),
      (∀ i (j : Fin (K i)), (e.symm ⟨i, j⟩).val = a i + j.val) ∧
      (∀ i (j : Fin (K i)), code (a i + j.val) = i) := by
  let fiber (i : I) : Finset ℕ := (Finset.range N).filter (fun n => code n = i)
  have hi (i : I) : ∃ a : ℕ, fiber i = Finset.Ico a (a + (fiber i).card) := by
    apply finite_convex_set_interval
    intro x hx y hy z hxz hzy
    obtain ⟨hxN, hxi⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyN, hyi⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hzy (Finset.mem_range.mp hyN)), ?_⟩
    exact (hc x y z (Finset.mem_range.mp hxN) (Finset.mem_range.mp hyN)
      hxz hzy (hxi.trans hyi.symm)).trans hxi
  choose a ha using hi
  let K : I → ℕ := fun i => (fiber i).card
  have hm (i : I) (n : ℕ) : n < N ∧ code n = i ↔ a i ≤ n ∧ n < a i + K i := by
    simpa only [fiber, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] using
      Iff.of_eq (congrArg (fun s : Finset ℕ => n ∈ s) (ha i))
  have hstart (n : Fin N) : a (code n.val) ≤ n.val :=
    ((hm (code n.val) n.val).mp ⟨n.isLt, rfl⟩).1
  let e : Fin N ≃ Σ i, Fin (K i) := {
    toFun := fun n => ⟨code n.val, ⟨n.val - a (code n.val), by
      have h := ((hm (code n.val) n.val).mp ⟨n.isLt, rfl⟩).2
      have ha := hstart n
      omega⟩⟩
    invFun := fun z => ⟨a z.1 + z.2.val, ((hm z.1 _).mpr ⟨by omega, by omega⟩).1⟩
    left_inv := by
      intro n
      apply Fin.ext
      exact Nat.add_sub_of_le (hstart n)
    right_inv := by
      rintro ⟨i, j⟩
      have hci : code (a i + j.val) = i :=
        ((hm i _).mpr ⟨by omega, by omega⟩).2
      apply Sigma.ext hci
      apply (Fin.heq_ext_iff (congrArg K hci)).mpr
      simp only [hci, Nat.add_sub_cancel_left]
  }
  refine ⟨a, K, e, ?_, ?_⟩
  · intro i j
    rfl
  · intro i j
    exact ((hm i _).mpr ⟨by omega, by omega⟩).2

end Ostmann

end OAI
