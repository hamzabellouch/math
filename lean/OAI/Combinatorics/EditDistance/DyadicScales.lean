import Mathlib

namespace OAI

/-!
# Dyadic scales for window displacement
-/

namespace EditDyadic

lemma log_mono {a b : ℕ} (hab : a ≤ b) : Nat.log 2 a ≤ Nat.log 2 b := by
  exact Nat.log_mono_right hab

lemma scale {l delta : ℕ} (hl : 0 < l) (hd : 0 < delta) (hdl : delta ≤ 2*l) :
    ∃ j : Fin (Nat.log 2 l+1),
      let s := 2^j.val
      1 ≤ s ∧ s ≤ l ∧ delta ≤ 16*s ∧ 2*(s-1)+s ≤ delta := by
  by_cases hsmall : delta < 4
  · refine ⟨⟨0,by omega⟩,?_⟩
    simp only [pow_zero]
    omega
  · let m := delta/4
    have hm : 0 < m := by dsimp [m]; omega
    have hml : m ≤ l := by dsimp [m]; omega
    have hj : Nat.log 2 m < Nat.log 2 l+1 := by have := log_mono hml; omega
    refine ⟨⟨Nat.log 2 m,hj⟩,?_⟩
    dsimp only
    have hs : 1 ≤ 2^Nat.log 2 m := Nat.one_le_pow _ _ (by omega)
    have hsm : 2^Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
    have hm2 := Nat.lt_pow_succ_log_self (by omega : 1 < 2) m
    rw [pow_succ] at hm2
    dsimp [m] at *
    refine ⟨hs,hsm.trans hml,?_,?_⟩ <;> omega

lemma scale_le {l : ℕ} (hl : 0 < l) (j : Fin (Nat.log 2 l+1)) : 2^j.val ≤ l := by
  exact (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : j.val ≤ Nat.log 2 l)).trans
    (Nat.pow_log_le_self 2 (by omega))

end EditDyadic

end OAI
