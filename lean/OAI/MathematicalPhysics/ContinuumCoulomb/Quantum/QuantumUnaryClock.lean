import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalInput
import Mathlib.Order.Fin.Basic
import Mathlib.Order.UpperLower.Basic

namespace OAI

/-! Unary clock states and the adjacent-pair characterization of validity. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaUnaryClock (N : ℕ) (t : Fin (N+1)) : SourceSpinBasis N :=
  fun i => if i.val < t.val then 1 else 0

theorem qmaUnaryClock_injective (N : ℕ) : Function.Injective (qmaUnaryClock N) := by
  intro s t h
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · let i : Fin N := ⟨s.val,lt_of_lt_of_le hst (Nat.le_of_lt_succ t.isLt)⟩
    have hi := congrFun h i
    have hs : ¬i.val < s.val := by simp [i]
    have ht : i.val < t.val := hst
    simp [qmaUnaryClock,hs,ht] at hi
  · let i : Fin N := ⟨t.val,lt_of_lt_of_le hts (Nat.le_of_lt_succ s.isLt)⟩
    have hi := congrFun h i
    have hs : i.val < s.val := hts
    have ht : ¬i.val < t.val := by simp [i]
    simp [qmaUnaryClock,hs,ht] at hi

theorem qmaUnaryClock_antitone (N : ℕ) (t : Fin (N+1)) : Antitone (qmaUnaryClock N t) := by
  intro i j hij
  by_cases hi : i.val < t.val
  · by_cases hj : j.val < t.val <;> simp [qmaUnaryClock,hi,hj]
  · have hj : ¬j.val < t.val := by omega
    simp [qmaUnaryClock,hi,hj]

theorem qmaUnaryClock_of_antitone (N : ℕ) (s : SourceSpinBasis N) (hs : Antitone s) :
    ∃ t : Fin (N+1), qmaUnaryClock N t = s := by
  have hlow : IsLowerSet {i : Fin N | s i = 1} := by
    intro j i hij hj
    have h := hs hij
    change s j = 1 at hj
    rw [hj] at h
    have hb := (s i).isLt
    apply Fin.ext
    change (s i).val = 1
    change (1 : Fin 2).val ≤ (s i).val at h
    norm_num at h
    omega
  rcases hlow.eq_univ_or_Iio with hall | ⟨t,ht⟩
  · refine ⟨Fin.last N,?_⟩
    funext i
    have hi : s i = 1 := by
      have hm : i ∈ ({j : Fin N | s j = 1} : Set (Fin N)) := by rw [hall]; trivial
      exact hm
    simp [qmaUnaryClock,i.isLt,hi]
  · refine ⟨⟨t.val,Nat.lt_succ_of_lt t.isLt⟩,?_⟩
    funext i
    have hi : s i = 1 ↔ i < t := Set.ext_iff.mp ht i
    by_cases hit : i.val < t.val
    · have hsi : s i = 1 := hi.mpr hit
      simp [qmaUnaryClock,hit,hsi]
    · have hsi : s i ≠ 1 := fun h => hit (hi.mp h)
      have hz : s i = 0 := by
        apply Fin.ext
        have hb := (s i).isLt
        have hn : (s i).val ≠ 1 := fun h => hsi (Fin.ext h)
        change (s i).val = 0
        omega
      simp [qmaUnaryClock,hit,hz]

end ContinuumCoulomb

end

end OAI
