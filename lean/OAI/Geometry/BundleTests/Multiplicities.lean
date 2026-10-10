import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-! Multiplicity sequences and their arithmetic identities. -/


namespace Kaplansky
open scoped BigOperators

def testMultiplicity (m R j : ℕ) (i : Fin (j+1)) : ℕ :=
  if i.val=0 then 64*m*4^(R-j) else 960*m*4^(R+2*i.val-j-2)

def testRank (m R j : ℕ) : ℕ := 4^j*(64*m*4^R)

theorem testRank_eq (m R j : ℕ) : testRank m R j = 64*m*4^(R+j) := by
  simp only [testRank,pow_add]
  ring

theorem testMultiplicity_pos {m : ℕ} (hm : 0<m) (R j : ℕ) (i : Fin (j+1)) :
    0<testMultiplicity m R j i := by
  unfold testMultiplicity
  split <;> positivity

theorem testMultiplicity_quarter {m R j : ℕ} (hj : j<R) (i : Fin (j+1)) :
    4*testMultiplicity m R (j+1) i.castSucc = testMultiplicity m R j i := by
  unfold testMultiplicity
  simp only [Fin.val_castSucc]
  split_ifs with hi
  · have he : R-j=(R-(j+1))+1 := by omega
    rw [he,pow_succ]
    ring
  · have he : R+2*i.val-j-2=(R+2*i.val-(j+1)-2)+1 := by omega
    rw [he,pow_succ]
    ring

theorem testMultiplicity_fresh {m R j : ℕ} (hj : j<R) :
    4*testMultiplicity m R (j+1) (Fin.last (j+1)) = 15*testRank m R j := by
  have hi : (Fin.last (j+1)).val ≠ 0 := by simp
  rw [testMultiplicity,ite_eq_right hi,testRank_eq]
  have he : R+j=(R+2*(Fin.last (j+1)).val-(j+1)-2)+1 := by
    simp only [Fin.val_last]
    omega
  rw [he,pow_succ]
  ring

theorem sum_testMultiplicity {m R j : ℕ} (hj : j≤R) :
    ∑ i, testMultiplicity m R j i = testRank m R j := by
  induction j with
  | zero => simp [testMultiplicity,testRank]
  | succ j ih =>
    have hlt : j<R := by omega
    have hprev := ih (by omega)
    have hq : 4*(∑ i : Fin (j+1), testMultiplicity m R (j+1) i.castSucc) =
        testRank m R j := by
      rw [Finset.mul_sum]
      simpa only [testMultiplicity_quarter hlt] using hprev
    rw [Fin.sum_univ_castSucc]
    have hf := testMultiplicity_fresh (m := m) hlt
    have hr : testRank m R (j+1)=4*testRank m R j := by
      simp only [testRank,pow_succ]
      ring
    rw [hr]
    omega

theorem testMultiplicity_divisible {m R j : ℕ} (hj : j<R) (i : Fin (j+1)) :
    4 ∣ testMultiplicity m R j i := ⟨_,(testMultiplicity_quarter hj i).symm⟩

theorem testMultiplicity_lower_bound {m R j : ℕ} (hj : j<R) (i : Fin (j+1)) :
    256*m ≤ testMultiplicity m R j i := by
  rw [← testMultiplicity_quarter hj i]
  have h : 64*m ≤ testMultiplicity m R (j+1) i.castSucc := by
    unfold testMultiplicity
    split
    · have hp : 1≤4^(R-(j+1)) := Nat.one_le_pow _ _ (by omega)
      nlinarith
    · have hp : 1≤4^(R+2*(i.castSucc).val-(j+1)-2) := Nat.one_le_pow _ _ (by omega)
      nlinarith
  omega

end Kaplansky

end OAI
