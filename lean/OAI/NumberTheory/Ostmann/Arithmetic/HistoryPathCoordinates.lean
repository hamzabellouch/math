import OAI.NumberTheory.Ostmann.Arithmetic.HistoryLinearization

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryLinearization
open Construction

def giants (a : State) : ℚ × ℚ := (a.giantPlus,a.giantMinus)

theorem supported_small_product_pos {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) :
    0 < (h.root.small.map SmallSlot.value).prod := by
  apply List.prod_pos
  intro n hn
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hn
  apply History.supported_root_positive hs
  simp only [State.values,List.mem_cons,List.mem_map]
  exact Or.inr (Or.inr ⟨q,hq,rfl⟩)

theorem supported_pivotRow_nonzero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    (pivotRow a u hp hm left.root.frequency right.root.frequency).1 ≠ 0 ∧
      (pivotRow a u hp hm left.root.frequency right.root.frequency).2 ≠ 0 := by
  have hprod := supported_small_product_pos hs
  simp only [History.root] at hprod
  rw [History.supported_small_product_split hs] at hprod
  have hp0 : ((hp.map SmallSlot.value).prod:ℚ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_mul_pos_right hprod).ne'
  have hm0 : ((hm.map SmallSlot.value).prod:ℚ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_mul_pos_left hprod).ne'
  have hs0 : (a.frequency:ℚ) ≠ 0 := by
    exact_mod_cast History.supported_root_frequency_ne_zero hs
  have hu0 : ((u.map SmallSlot.value).prod:ℚ) ≠ 0 := by
    exact_mod_cast (History.supported_compensation_product_pos hs).ne'
  have hv0 : (left.root.frequency:ℚ) ≠ 0 := by
    exact_mod_cast History.supported_root_frequency_ne_zero (History.supported_left hs)
  have hw0 : (right.root.frequency:ℚ) ≠ 0 := by
    exact_mod_cast History.supported_root_frequency_ne_zero (History.supported_right hs)
  exact ⟨div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hw0) hp0) (mul_ne_zero hs0 hu0),
    div_ne_zero (mul_ne_zero hv0 hm0) (mul_ne_zero hs0 hu0)⟩

def leftTransition {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    (ℚ × ℚ) ≃ₗ[ℚ] (ℚ × ℚ) :=
  LinearReversal.leftStep
    (pivotRow a u hp hm left.root.frequency right.root.frequency).1
    (pivotRow a u hp hm left.root.frequency right.root.frequency).2
    (supported_pivotRow_nonzero hs).2

def rightTransition {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    (ℚ × ℚ) ≃ₗ[ℚ] (ℚ × ℚ) :=
  LinearReversal.rightStep
    (pivotRow a u hp hm left.root.frequency right.root.frequency).1
    (pivotRow a u hp hm left.root.frequency right.root.frequency).2
    (supported_pivotRow_nonzero hs).1

theorem leftTransition_giants {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    leftTransition hs (giants a) = giants left.root := by
  obtain ⟨hlp,hrp,hlm,hrm⟩ := History.supported_child_giants hs
  apply Prod.ext
  · change _ = (left.root.giantPlus:ℚ)
    rw [hlp]
    exact (supported_pivot_linear hs).symm
  · change (a.giantPlus:ℚ) = (left.root.giantMinus:ℚ)
    rw [hlm]

theorem rightTransition_giants {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    rightTransition hs (giants a) = giants right.root := by
  obtain ⟨hlp,hrp,hlm,hrm⟩ := History.supported_child_giants hs
  apply Prod.ext
  · change _ = (right.root.giantPlus:ℚ)
    rw [hrp]
    exact (supported_pivot_linear hs).symm
  · change (a.giantMinus:ℚ) = (right.root.giantMinus:ℚ)
    rw [hrm]

def leafStateAt : {l : ℕ} → History l → (Fin l → Bool) → State
  | 0, .leaf a, _ => a
  | _+1, .node _ _ _ _ _ left right, path =>
      if path 0 then leafStateAt right (Fin.tail path) else leafStateAt left (Fin.tail path)

def leafEquiv (V : ℕ → ℕ) (outside : List ℕ) :
    {l : ℕ} → (h : History l) → h.Supported V outside →
      (Fin l → Bool) → (ℚ × ℚ) ≃ₗ[ℚ] (ℚ × ℚ)
  | 0, .leaf _, _, _ => LinearEquiv.refl ℚ (ℚ × ℚ)
  | _+1, .node _ _ _ _ _ left right, hs, path =>
      if path 0 then (rightTransition hs).trans
        (leafEquiv V outside right (History.supported_right hs) (Fin.tail path))
      else (leftTransition hs).trans
        (leafEquiv V outside left (History.supported_left hs) (Fin.tail path))

theorem leafEquiv_giants {V : ℕ → ℕ} {outside : List ℕ} {l : ℕ}
    (h : History l) (hs : h.Supported V outside) (path : Fin l → Bool) :
    leafEquiv V outside h hs path (giants h.root) = giants (leafStateAt h path) := by
  induction h with
  | leaf a => rfl
  | @node l a p u hp hm left right ihl ihr =>
      simp only [leafEquiv,leafStateAt,History.root]
      split_ifs
      · rw [LinearEquiv.trans_apply,rightTransition_giants]
        exact ihr (History.supported_right hs) (Fin.tail path)
      · rw [LinearEquiv.trans_apply,leftTransition_giants]
        exact ihl (History.supported_left hs) (Fin.tail path)

end Ostmann.Arithmetic.HistoryLinearization

end

end OAI
