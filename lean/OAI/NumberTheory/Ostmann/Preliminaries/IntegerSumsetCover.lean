import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.List.Basic
import OAI.NumberTheory.Ostmann.Preliminaries.CyclicSumsetCover

namespace OAI

/-! # Lifting cyclic covering to exact integer sums

The bounded cyclic word can be padded with zero and the upper endpoint. This
is the finite, exact version of the good-cell interior sumset argument.
-/

namespace Ostmann

open scoped BigOperators

/-- A cyclic cover by `r` summands covers the interior interval with any
prescribed longer number of summands. -/
theorem integer_interval_sum_cover (A : Finset ℕ) (s r n : ℕ)
    (hs : 0 < s) (h0 : 0 ∈ A) (hend : s ∈ A)
    (hbound : ∀ a ∈ A, a ≤ s) (hrn : r ≤ n)
    (hcover : ∀ x : ZMod s, ∃ f : Fin r → ℕ,
      (∀ i, f i ∈ A) ∧ ∑ i, (f i : ZMod s) = x)
    (t : ℕ) (hlo : r * s ≤ t) (hhi : t ≤ (n - r) * s) :
    ∃ w : List ℕ, w.length = n ∧ (∀ a ∈ w, a ∈ A) ∧ w.sum = t := by
  obtain ⟨f, hf, hft⟩ := hcover (t : ZMod s)
  let b := ∑ i, f i
  have hb : b ≤ r * s := by
    calc
      b ≤ ∑ _i : Fin r, s := Finset.sum_le_sum (fun i _ => hbound _ (hf i))
      _ = r * s := by simp
  have hbt : b ≤ t := hb.trans hlo
  have hcast : ((t - b : ℕ) : ZMod s) = 0 := by
    rw [Nat.cast_sub hbt]
    have hbcast : (b : ZMod s) = (t : ZMod s) := by
      simpa only [b, Nat.cast_sum] using hft
    rw [hbcast, sub_self]
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff (t - b) s).mp hcast
  have heq : b + k * s = t := by
    rw [Nat.mul_comm s k] at hk
    omega
  have hkbound : k ≤ n - r := by nlinarith
  let w := List.ofFn f ++ List.replicate k s ++ List.replicate (n - r - k) 0
  refine ⟨w, ?_, ?_, ?_⟩
  · simp only [w, List.length_append, List.length_ofFn, List.length_replicate]
    omega
  · intro a ha
    simp only [w, List.mem_append, List.mem_ofFn, List.mem_replicate] at ha
    rcases ha with (⟨i, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · exact hf i
    · exact hend
    · exact h0
  · simpa [w, List.sum_append, List.sum_replicate, List.sum_ofFn, b] using heq

/-- The tuple version of the cyclic covering theorem lifts through the actual
residue image of a finite set of nonnegative integers. -/
theorem lift_cyclic_sum_cover (A : Finset ℕ) (s r : ℕ)
    (hcover : ∀ x : ZMod s, ∃ f : Fin r → ZMod s,
      (∀ i, f i ∈ A.image (fun a : ℕ => (a : ZMod s))) ∧ ∑ i, f i = x) :
    ∀ x : ZMod s, ∃ f : Fin r → ℕ,
      (∀ i, f i ∈ A) ∧ ∑ i, (f i : ZMod s) = x := by
  classical
  intro x
  obtain ⟨f, hf, hsum⟩ := hcover x
  have hex : ∀ i, ∃ a ∈ A, (a : ZMod s) = f i := fun i => Finset.mem_image.mp (hf i)
  choose a ha he using hex
  exact ⟨a, ha, by simpa only [he] using hsum⟩

end Ostmann

end OAI
