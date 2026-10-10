import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConjugateWindowStabilization
import Mathlib.GroupTheory.Finiteness

namespace OAI

/-! # Finite generation of the full cyclic-conjugate subgroup

A stable finite conjugate window contains all integer conjugates. Combined
with polynomial-growth stabilization, this is an actual finite-generation
theorem, with no assumed kernel-finiteness input.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

def cyclicConjugateSubgroup (t : G) (R : Finset G) : Subgroup G :=
  Subgroup.closure {x | ∃ k : ℤ, ∃ r ∈ R, t ^ k * r * t ^ (-k) = x}

omit [DecidableEq G] in
theorem cyclic_conjugation_add (t : G) (j k : ℤ) (r : G) :
    t ^ j * (t ^ k * r * t ^ (-k)) * t ^ (-j) =
      t ^ (j + k) * r * t ^ (-(j + k)) := by
  rw [show -(j + k) = -k + -j by omega, zpow_add, zpow_add]
  simp only [mul_assoc]

theorem conjugateWindow_conjugation (t : G) (R : Finset G) (n : ℕ)
    {j : ℤ} (hj : -1 ≤ j ∧ j ≤ 1) {x : G} (hx : x ∈ conjugateWindow t R n) :
    t ^ j * x * t ^ (-j) ∈ conjugateWindow t R (n + 1) := by
  obtain ⟨k, hk, hx⟩ := mem_biUnion.mp hx
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hx
  rw [cyclic_conjugation_add]
  apply mem_biUnion.mpr
  refine ⟨j + k, mem_Icc.mpr ?_, mem_image.mpr ⟨r, hr, rfl⟩⟩
  have hk' := mem_Icc.mp hk
  constructor <;> omega

theorem conjugateWindowSubgroup_conjugation (t : G) (R : Finset G) (n : ℕ)
    {j : ℤ} (hj : -1 ≤ j ∧ j ≤ 1) {x : G} (hx : x ∈ conjugateWindowSubgroup t R n) :
    t ^ j * x * t ^ (-j) ∈ conjugateWindowSubgroup t R (n + 1) := by
  let f := (MulAut.conj (t ^ j)).toMonoidHom
  have hle : conjugateWindowSubgroup t R n ≤
      (conjugateWindowSubgroup t R (n + 1)).comap f := by
    apply (Subgroup.closure_le _).mpr
    intro y hy
    change t ^ j * y * (t ^ j)⁻¹ ∈ conjugateWindowSubgroup t R (n + 1)
    rw [← zpow_neg]
    exact Subgroup.subset_closure (conjugateWindow_conjugation t R n hj hy)
  have hh := hle hx
  change t ^ j * x * (t ^ j)⁻¹ ∈ conjugateWindowSubgroup t R (n + 1) at hh
  simpa only [← zpow_neg] using hh

theorem stable_conjugateWindow_eq_full (t : G) (R : Finset G) (n : ℕ)
    (he : conjugateWindowSubgroup t R n = conjugateWindowSubgroup t R (n + 1)) :
    cyclicConjugateSubgroup t R = conjugateWindowSubgroup t R n := by
  have hR (r : G) (hr : r ∈ R) : r ∈ conjugateWindowSubgroup t R n := by
    apply Subgroup.subset_closure
    apply mem_biUnion.mpr
    refine ⟨0, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    exact mem_image.mpr ⟨r, hr, by simp⟩
  have hstep (j : ℤ) (hj : -1 ≤ j ∧ j ≤ 1) (x : G)
      (hx : x ∈ conjugateWindowSubgroup t R n) :
      t ^ j * x * t ^ (-j) ∈ conjugateWindowSubgroup t R n := by
    rw [he]
    exact conjugateWindowSubgroup_conjugation t R n hj hx
  have hpos (r : G) (hr : r ∈ R) (k : ℕ) :
      t ^ (k : ℤ) * r * t ^ (-(k : ℤ)) ∈ conjugateWindowSubgroup t R n := by
    induction k with
    | zero => simpa using hR r hr
    | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℤ) = 1 + (k : ℤ) by omega, ← cyclic_conjugation_add]
      exact hstep 1 (by omega) _ ih
  have hneg (r : G) (hr : r ∈ R) (k : ℕ) :
      t ^ (-(k : ℤ)) * r * t ^ (-(-(k : ℤ))) ∈ conjugateWindowSubgroup t R n := by
    induction k with
    | zero => simpa using hR r hr
    | succ k ih =>
      rw [show -((k + 1 : ℕ) : ℤ) = -1 + -(k : ℤ) by omega, ← cyclic_conjugation_add]
      exact hstep (-1) (by omega) _ ih
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨k, r, hr, rfl⟩
    cases k with
    | ofNat k => exact hpos r hr k
    | negSucc k => exact hneg r hr (k + 1)
  · apply Subgroup.closure_mono
    intro x hx
    obtain ⟨k, _, hx⟩ := mem_biUnion.mp hx
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hx
    exact ⟨k, r, hr, rfl⟩

theorem cyclicConjugateSubgroup_fg_of_polynomial_growth
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (t : G) (R : Finset G) : (cyclicConjugateSubgroup t R).FG := by
  obtain ⟨n, hn⟩ := exists_stable_conjugate_window S hS hgen hvol t R
  rw [stable_conjugateWindow_eq_full t R n hn]
  exact ⟨conjugateWindow t R n, rfl⟩

end PolycyclicRecognition

end

end OAI
