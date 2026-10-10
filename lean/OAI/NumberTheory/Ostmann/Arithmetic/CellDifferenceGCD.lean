import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Int.GCD
import OAI.NumberTheory.Ostmann.Preliminaries.CyclicSumsetCover

namespace OAI

/-! # GCD normalization of cell differences

Finite cell differences divided by their gcd generate every cyclic quotient.
Reducing a set contained in `[0,s]` modulo `s` loses at most the upper endpoint.
-/

namespace Ostmann

open scoped BigOperators

private theorem nat_gcd_mem_subgroup {q : ℕ} (H : AddSubgroup (ZMod q))
    (a b : ℕ) (ha : (a : ZMod q) ∈ H) (hb : (b : ZMod q) ∈ H) :
    (a.gcd b : ZMod q) ∈ H := by
  have he : (a.gcd b : ZMod q) =
      (Nat.gcdA a b) • (a : ZMod q) + (Nat.gcdB a b) • (b : ZMod q) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod q)) (Nat.gcd_eq_gcd_ab a b)
    simpa [zsmul_eq_mul, mul_comm] using hh
  rw [he]
  exact H.add_mem (H.zsmul_mem ha _) (H.zsmul_mem hb _)

private theorem finset_gcd_mem_subgroup {q : ℕ} (H : AddSubgroup (ZMod q))
    (A : Finset ℕ) (hA : ∀ a ∈ A, (a : ZMod q) ∈ H) :
    ((A.gcd id : ℕ) : ZMod q) ∈ H := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    rw [Finset.gcd_insert]
    exact nat_gcd_mem_subgroup H a (A.gcd id) (hA a (Finset.mem_insert_self _ _))
      (ih (fun b hb => hA b (Finset.mem_insert_of_mem hb)))

/-- A gcd-one set of nonnegative integers generates every cyclic quotient. -/
theorem cyclic_closure_of_gcd_one (A : Finset ℕ) (hA : A.gcd id = 1) (q : ℕ) :
    AddSubgroup.closure ((A.image (fun a : ℕ => (a : ZMod q)) : Finset (ZMod q)) : Set (ZMod q)) = ⊤ := by
  let H := AddSubgroup.closure ((A.image (fun a : ℕ => (a : ZMod q)) : Finset (ZMod q)) : Set (ZMod q))
  have h1 : (1 : ZMod q) ∈ H := by
    have hh := finset_gcd_mem_subgroup H A (fun a ha =>
      AddSubgroup.subset_closure (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
    simpa [hA] using hh
  apply top_unique
  intro x _
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  change (z : ZMod q) ∈ H
  simpa only [zsmul_one] using H.zsmul_mem h1 z

/-- GCD normalization gives the required generating set without a primitivity
assumption on the original cell indices. -/
theorem normalized_cyclic_closure (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) (ha0 : a ≠ 0)
    (q : ℕ) :
    AddSubgroup.closure
      ((A.image (fun b => b / A.gcd id)).image (fun b : ℕ => (b : ZMod q)) : Set (ZMod q)) = ⊤ := by
  apply cyclic_closure_of_gcd_one
  rw [Finset.gcd_image]
  exact Finset.gcd_div_id_eq_one ha ha0

/-- The only collision introduced on `[0,s]` by reduction modulo `s` is
between the two endpoints. -/
theorem card_residue_image_lower (A : Finset ℕ) (s : ℕ) (_hs : 0 < s)
    (hbound : ∀ a ∈ A, a ≤ s) :
    A.card ≤ (A.image (fun a : ℕ => (a : ZMod s))).card + 1 := by
  have hinj : Set.InjOn (fun a : ℕ => (a : ZMod s)) (A.erase s) := by
    intro a ha b hb hab
    have hat : a < s := lt_of_le_of_ne (hbound a (Finset.mem_of_mem_erase ha))
      (Finset.ne_of_mem_erase ha)
    have hbt : b < s := lt_of_le_of_ne (hbound b (Finset.mem_of_mem_erase hb))
      (Finset.ne_of_mem_erase hb)
    have hh := (ZMod.natCast_eq_natCast_iff' a b s).mp hab
    simpa only [Nat.mod_eq_of_lt hat, Nat.mod_eq_of_lt hbt] using hh
  have hc := Finset.card_image_iff.mpr hinj
  have hle := Finset.card_le_card (Finset.image_subset_image
    (f := fun a : ℕ => (a : ZMod s)) (Finset.erase_subset s A))
  rw [hc] at hle
  by_cases hmem : s ∈ A
  · have he := Finset.card_erase_add_one hmem
    omega
  · simpa [Finset.erase_eq_of_notMem hmem] using hle.trans (Nat.le_succ _)

end Ostmann

end OAI
