import OAI.Algebra.OddKaplansky.SimplexCount

namespace OAI

section

namespace OddKaplansky.Augmentation
noncomputable section
open scoped Classical BigOperators
variable (p ell : ℕ) [sectionInstance38 : Fact p.Prime]

lemma complement_lt
    (p : Nat)
    [Fact (Nat.Prime p)] (n : Fin p) : p-1-n.val < p := by have := n.isLt; omega
lemma complement_complement
    (p : Nat)
    [Fact (Nat.Prime p)] (n : Fin p) : p-1-(p-1-n.val) = n.val := by have := n.isLt; omega

def highEquivDeficit : High (E := Fin 3) p ell ≃ SimplexCount.Deficit p ell where
  toFun n := ⟨fun i => ⟨p-1-(n.val i).val, complement_lt p (n.val i)⟩,by
    have hn := n.property
    have h0 := (n.val 0).isLt; have h1 := (n.val 1).isLt; have h2 := (n.val 2).isLt
    simp [Fin.sum_univ_succ] at hn ⊢
    omega⟩
  invFun n := ⟨fun i => ⟨p-1-(n.val i).val, complement_lt p (n.val i)⟩,by
    have hn := n.property
    have h0 := (n.val 0).isLt; have h1 := (n.val 1).isLt; have h2 := (n.val 2).isLt
    simp [Fin.sum_univ_succ] at hn ⊢
    omega⟩
  left_inv n := by ext i; exact complement_complement p (n.val i)
  right_inv n := by ext i; exact complement_complement p (n.val i)

lemma card_high (hl : ell ≤ p) : Fintype.card (High (E := Fin 3) p ell) = (ell+2).choose 3 := by
  rw [Fintype.card_congr (highEquivDeficit p ell),SimplexCount.card_deficit p ell hl]

lemma card_high_le
    (p : Nat)
    (ell : Nat)
    [Fact (Nat.Prime p)] : Fintype.card (High (E := Fin 3) p ell) ≤ p^3 := by
  calc
    _ ≤ Fintype.card (Fin 3 → Fin p) := Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp

lemma high_ratio (hp : p = 2*ell+1) (hl : 1 ≤ ell) :
    p^3 < 48*Fintype.card (High (E := Fin 3) p ell) := by
  have he : ell ≤ p := by omega
  rw [card_high p ell he, ← SimplexCount.card_tetrahedron]
  have hc := SimplexCount.six_tetrahedron ell
  rw [hp]
  nlinarith

end
end OddKaplansky.Augmentation

end

end OAI
