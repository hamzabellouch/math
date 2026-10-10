import OAI.Algebra.OddKaplansky.AugmentationMatrices

namespace OAI

section
namespace OddKaplansky.SimplexCount
noncomputable section
open scoped Classical BigOperators

abbrev Triangle (ell : ℕ) := Σ a : Fin ell, Fin (ell-a.val)
abbrev Tetrahedron (ell : ℕ) := Σ a : Fin ell, Triangle (ell-a.val)

lemma card_triangle_succ (ell : ℕ) : Fintype.card (Triangle (ell+1)) = ell+1+Fintype.card (Triangle ell) := by
  simp only [Triangle, Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_succ,
    Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]
lemma card_tetrahedron_succ (ell : ℕ) : Fintype.card (Tetrahedron (ell+1)) =
    Fintype.card (Triangle (ell+1))+Fintype.card (Tetrahedron ell) := by
  conv_lhs => rw [Fintype.card_sigma]
  conv_rhs => arg 2; rw [Fintype.card_sigma]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]
  rfl

lemma card_triangle (ell : ℕ) : Fintype.card (Triangle ell) = (ell+1).choose 2 := by
  induction ell with
  | zero => simp [Triangle]
  | succ ell ih =>
    rw [card_triangle_succ,ih]
    simpa [Nat.choose_one_right,add_comm] using (Nat.choose_succ_succ (ell+1) 1).symm
lemma card_tetrahedron (ell : ℕ) : Fintype.card (Tetrahedron ell) = (ell+2).choose 3 := by
  induction ell with
  | zero => simp [Tetrahedron]
  | succ ell ih =>
    rw [card_tetrahedron_succ,card_triangle,ih]
    simpa [add_comm,add_left_comm,add_assoc] using (Nat.choose_succ_succ (ell+2) 2).symm

abbrev Deficit (p ell : ℕ) := {a : Fin 3 → Fin p // ∑ i, (a i).val < ell}

def deficitEquiv (p ell : ℕ) (hl : ell ≤ p) : Deficit p ell ≃ Tetrahedron ell where
  toFun a := by
    have ha := a.property
    simp [Fin.sum_univ_succ] at ha
    refine ⟨⟨(a.val 0).val, by omega⟩, ⟨⟨(a.val 1).val, ?_⟩, ⟨(a.val 2).val, ?_⟩⟩⟩
    · change (a.val 1).val < ell - (a.val 0).val
      omega
    · change (a.val 2).val < ell - (a.val 0).val - (a.val 1).val
      omega
  invFun a := ⟨![⟨a.1.val, a.1.isLt.trans_le hl⟩,
    ⟨a.2.1.val, by have := a.2.1.isLt; omega⟩,
    ⟨a.2.2.val, by have := a.2.2.isLt; omega⟩],by
      have := a.1.isLt; have := a.2.1.isLt; have := a.2.2.isLt
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Matrix.cons_val_fin_one,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
      omega⟩
  left_inv a := by ext i; fin_cases i <;> rfl
  right_inv a := by rcases a with ⟨a,b,c⟩; rfl

lemma card_deficit (p ell : ℕ) (hl : ell ≤ p) : Fintype.card (Deficit p ell) = (ell+2).choose 3 := by
  rw [Fintype.card_congr (deficitEquiv p ell hl),card_tetrahedron]

lemma twice_triangle (ell : ℕ) : 2*Fintype.card (Triangle ell) = ell*(ell+1) := by
  induction ell with
  | zero => simp [Triangle]
  | succ ell ih => rw [card_triangle_succ]; nlinarith
lemma six_tetrahedron (ell : ℕ) : 6*Fintype.card (Tetrahedron ell) = ell*(ell+1)*(ell+2) := by
  induction ell with
  | zero => simp [Tetrahedron]
  | succ ell ih =>
    rw [card_tetrahedron_succ]
    have h := twice_triangle (ell+1)
    nlinarith

end
end OddKaplansky.SimplexCount

end

end OAI
