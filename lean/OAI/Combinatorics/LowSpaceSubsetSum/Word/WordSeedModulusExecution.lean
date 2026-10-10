import Mathlib.Data.Nat.Log

namespace OAI

/-! # Computing a rejection range width and its cached modulus

A doubling cursor starts at one and stops at the first power of two at
least the requested range size. The width and modulus are computed together.
-/

namespace LowSpaceSubsetSum.WordSeedModulusExecution

structure Result where
  width : ℕ
  modulus : ℕ
  work : ℕ

def loop (D : ℕ) : ℕ → ℕ → ℕ → ℕ → Result
  | 0, width, modulus, work => ⟨width,modulus,work+1⟩
  | fuel+1, width, modulus, work =>
      if modulus < D then loop D fuel (width+1) (2*modulus) (work+5)
      else ⟨width,modulus,work+1⟩

theorem loop_value (D fuel width modulus work : ℕ)
    (hm : modulus = 2^width) (hw : width ≤ Nat.clog 2 D)
    (hf : Nat.clog 2 D ≤ width+fuel) :
    loop D fuel width modulus work =
      ⟨Nat.clog 2 D,2^Nat.clog 2 D,work+5*(Nat.clog 2 D-width)+1⟩ := by
  induction fuel generalizing width modulus work with
  | zero =>
    have he : width = Nat.clog 2 D := by omega
    subst width
    subst modulus
    simp only [loop,Nat.sub_self,Nat.mul_zero,Nat.add_zero]
  | succ fuel ih =>
    change (if modulus < D then loop D fuel (width+1) (2*modulus) (work+5)
      else ⟨width,modulus,work+1⟩) = _
    split
    next h =>
      have hlt : width < Nat.clog 2 D := by
        exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (hm ▸ h)
      have hm' : 2*modulus = 2^(width+1) := by rw [hm,Nat.pow_succ]; omega
      rw [ih _ _ _ hm' (by omega) (by omega)]
      congr 1
      omega
    next h =>
      have hge : Nat.clog 2 D ≤ width := by
        apply Nat.clog_le_of_le_pow
        omega
      have he : width = Nat.clog 2 D := by omega
      subst width
      subst modulus
      simp only [Nat.sub_self,Nat.mul_zero,Nat.add_zero]

def run (D : ℕ) : Result := loop D D 0 1 0

theorem run_value (D : ℕ) : run D = ⟨Nat.clog 2 D,2^Nat.clog 2 D,5*Nat.clog 2 D+1⟩ := by
  have hf : Nat.clog 2 D ≤ D := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  simpa only [run,Nat.pow_zero,Nat.zero_add,Nat.sub_zero] using
    loop_value D D 0 1 0 (by simp) (Nat.zero_le _) (by omega)

theorem run_width (D : ℕ) : (run D).width = Nat.clog 2 D := by rw [run_value]

theorem run_modulus (D : ℕ) : (run D).modulus = 2^Nat.clog 2 D := by rw [run_value]

theorem run_work (D : ℕ) : (run D).work = 5*Nat.clog 2 D+1 := by rw [run_value]

theorem run_modulus_fits (D w : ℕ) (hw : Nat.clog 2 D < w) :
    (run D).modulus < 2^w := by
  rw [run_modulus]
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) hw

end LowSpaceSubsetSum.WordSeedModulusExecution

end OAI
