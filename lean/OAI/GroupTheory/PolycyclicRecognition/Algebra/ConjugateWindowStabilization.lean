import OAI.GroupTheory.PolycyclicRecognition.Analysis.ShortSubgroupChains
import Mathlib.Data.Int.Interval

namespace OAI

/-! # A stable finite window of cyclic conjugates

Polynomial word growth rules out strict growth at every conjugate window.
This is the finite-generation step for the kernel of a cyclic quotient.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

def conjugateWindow (t : G) (R : Finset G) (n : ℕ) : Finset G :=
  (Icc (-(n : ℤ)) (n : ℤ)).biUnion (fun k => R.image (fun r => t ^ k * r * t ^ (-k)))

def conjugateWindowSubgroup (t : G) (R : Finset G) (n : ℕ) : Subgroup G :=
  Subgroup.closure (conjugateWindow t R n : Set G)

theorem conjugateWindow_mono (t : G) (R : Finset G) : Monotone (conjugateWindow t R) := by
  intro n m hnm x hx
  obtain ⟨k, hk, hx⟩ := mem_biUnion.mp hx
  apply mem_biUnion.mpr
  refine ⟨k, mem_Icc.mpr ?_, hx⟩
  have hk' := mem_Icc.mp hk
  constructor <;> omega

theorem conjugateWindowSubgroup_mono (t : G) (R : Finset G) :
    Monotone (conjugateWindowSubgroup t R) := by
  intro n m hnm
  exact Subgroup.closure_mono (conjugateWindow_mono t R hnm)

theorem pow_mem_wordBall {S : Finset G} {m : ℕ} {t : G}
    (ht : t ∈ wordBall S m) (n : ℕ) : t ^ n ∈ wordBall S (m * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    simpa only [Nat.mul_add, Nat.mul_one] using mul_mem_wordBall ih ht

theorem zpow_mem_wordBall {S : Finset G} (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    {m : ℕ} {t : G} (ht : t ∈ wordBall S m) (k : ℤ) :
    t ^ k ∈ wordBall S (m * k.natAbs) := by
  cases k with
  | ofNat n => simpa using pow_mem_wordBall ht n
  | negSucc n => simpa using inv_mem_wordBall hS (pow_mem_wordBall ht (n + 1))

theorem conjugateWindow_word_bound {S : Finset G} (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (t : G) (R : Finset G) (m : ℕ) (ht : t ∈ wordBall S m)
    (hR : ∀ r ∈ R, r ∈ wordBall S m) (n : ℕ) :
    conjugateWindow t R n ⊆ wordBall S (m * (2 * n + 1)) := by
  intro x hx
  obtain ⟨k, hk, hx⟩ := mem_biUnion.mp hx
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hx
  have hk' := mem_Icc.mp hk
  have ha : k.natAbs ≤ n := by omega
  have h := mul_mem_wordBall (mul_mem_wordBall (zpow_mem_wordBall hS ht k) (hR r hr))
    (zpow_mem_wordBall hS ht (-k))
  apply wordBall_mono S _ h
  simp only [Int.natAbs_neg]
  nlinarith

theorem exists_stable_conjugate_window
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (t : G) (R : Finset G) :
    ∃ n, conjugateWindowSubgroup t R n = conjugateWindowSubgroup t R (n + 1) := by
  let m := (insert t R).sup (cayleyWordLength S hS hgen)
  have hm (x : G) (hx : x ∈ insert t R) : x ∈ wordBall S m :=
    (cayleyWordLength_le_iff S hS hgen x m).mp (le_sup hx)
  have ht := hm t (mem_insert_self t R)
  have hR := fun r hr => hm r (mem_insert_of_mem hr)
  have hmono := conjugateWindowSubgroup_mono t R
  by_contra! hneq
  apply polynomial_growth_forbids_short_strict_chain S hvol
    (conjugateWindowSubgroup t R) (fun n => hmono (Nat.le_succ n)) (3 * m)
  intro n
  have hex : ∃ x ∈ conjugateWindow t R (n + 1), x ∉ conjugateWindowSubgroup t R n := by
    by_contra! h
    have hle : conjugateWindowSubgroup t R (n + 1) ≤ conjugateWindowSubgroup t R n :=
      (Subgroup.closure_le _).mpr h
    exact hneq n (le_antisymm (hmono (Nat.le_succ n)) hle)
  obtain ⟨x, hx, hx'⟩ := hex
  refine ⟨x, Subgroup.subset_closure hx, hx', ?_⟩
  apply wordBall_mono S _ (conjugateWindow_word_bound hS t R m ht hR (n + 1) hx)
  nlinarith

end PolycyclicRecognition

end

end OAI
