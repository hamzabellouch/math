import Mathlib

namespace OAI

section
noncomputable section
open scoped Classical

namespace Subgroup
open scoped _root_.Subgroup
variable {Γ : Type*} [Group Γ]

def relativeMass (A B : Subgroup Γ) : ℝ := (B.relIndex A : ℝ) / (A.relIndex B : ℝ)

lemma relativeMass_eq_of_le {I A B : Subgroup Γ} (hIA : I ≤ A) (hIB : I ≤ B)
    (hI : I.relIndex A ≠ 0) :
    relativeMass A B = (I.relIndex A : ℝ) / (I.relIndex B : ℝ) := by
  have ha := _root_.Subgroup.relIndex_mul_relIndex I (A ⊓ B) A (le_inf hIA hIB) inf_le_left
  have hb := _root_.Subgroup.relIndex_mul_relIndex I (A ⊓ B) B (le_inf hIA hIB) inf_le_right
  have hi : I.relIndex (A ⊓ B) ≠ 0 := by
    intro hi
    rw [hi,zero_mul] at ha
    exact hI ha.symm
  have hir : (I.relIndex (A ⊓ B) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hi
  rw [_root_.Subgroup.inf_relIndex_left] at ha
  rw [_root_.Subgroup.inf_relIndex_right] at hb
  unfold relativeMass
  calc
    _ = ((I.relIndex (A ⊓ B) : ℝ) * (B.relIndex A : ℝ)) /
        ((I.relIndex (A ⊓ B) : ℝ) * (A.relIndex B : ℝ)) :=
      (mul_div_mul_left _ _ hir).symm
    _ = _ := by simp only [← Nat.cast_mul,ha,hb]

lemma relativeMass_pos {A B : Subgroup Γ} (hab : A.relIndex B ≠ 0)
    (hba : B.relIndex A ≠ 0) : 0 < relativeMass A B :=
  div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hba)) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hab))

lemma relativeMass_cocycle (A B C : Subgroup Γ)
    (hab : A.relIndex B ≠ 0) (hba : B.relIndex A ≠ 0)
    (hca : C.relIndex A ≠ 0) (hcb : C.relIndex B ≠ 0) :
    relativeMass A B * relativeMass B C = relativeMass A C := by
  let I := A ⊓ B ⊓ C
  have hIA : I ≤ A := inf_le_left.trans inf_le_left
  have hIB : I ≤ B := inf_le_left.trans inf_le_right
  have hIC : I ≤ C := inf_le_right
  have hI0A : I.relIndex A ≠ 0 :=
    _root_.Subgroup.relIndex_inf_ne_zero (by simpa only [_root_.Subgroup.inf_relIndex_left] using hba) hca
  have hI0B : I.relIndex B ≠ 0 :=
    _root_.Subgroup.relIndex_inf_ne_zero (by simpa only [_root_.Subgroup.inf_relIndex_right] using hab) hcb
  rw [relativeMass_eq_of_le hIA hIB hI0A,relativeMass_eq_of_le hIB hIC hI0B,
    relativeMass_eq_of_le hIA hIC hI0A]
  exact div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr hI0B)

lemma relativeMass_self (A : Subgroup Γ) : relativeMass A A = 1 := by
  simp [relativeMass]

end Subgroup
end
end

end OAI
