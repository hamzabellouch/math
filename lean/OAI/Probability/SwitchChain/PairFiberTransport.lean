import OAI.Probability.SwitchChain.PairFiberBridge

namespace OAI

noncomputable section
namespace Problem315.PairFiber

variable {V : Type*} [Fintype V]

theorem trade_eq_of_key_eq {G H : SimpleGraph V} {i j : V}
    (hij : i ≠ j) (hk : key i j G = key i j H) (T : Finset V)
    (hG : T ⊆ singletonSet G i j) (hH : T ⊆ singletonSet H i j) :
    trade G i j hij T hG = trade H i j hij T hH := by
  apply graph_eq_of_key_leftSet_eq
  · exact (key_trade G i j hij T hG).trans
      (hk.trans (key_trade H i j hij T hH).symm)
  · rw [leftSet_trade, leftSet_trade]

def assignmentEquivOfKeyEq {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} {i j : Fin n} (hij : i ≠ j)
    (hk : key i j G.val = key i j H.val) :
    Assignment G.val i j ≃ Assignment H.val i j := by
  have hs := singletonSet_eq_of_key_eq hk
  have hc := (leftSet_card_eq_iff_degree_eq hij hk).mpr
    ((G.property i).trans (H.property i).symm)
  exact
    { toFun := fun T => ⟨T.val, by simpa only [← hs, ← hc] using T.property⟩
      invFun := fun T => ⟨T.val, by simpa only [hs, hc] using T.property⟩
      left_inv := fun T => by apply Subtype.ext; rfl
      right_inv := fun T => by apply Subtype.ext; rfl }

@[simp] theorem assignmentEquivOfKeyEq_val {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} {i j : Fin n} (hij : i ≠ j)
    (hk : key i j G.val = key i j H.val) (T : Assignment G.val i j) :
    (assignmentEquivOfKeyEq hij hk T).val = T.val := rfl

theorem stateFiberEquiv_symm_eq_of_key_eq {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} {i j : Fin n} (hij : i ≠ j)
    (hk : key i j G.val = key i j H.val) (T : Assignment G.val i j) :
    ((stateFiberEquiv G i j hij).symm T).val =
      ((stateFiberEquiv H i j hij).symm (assignmentEquivOfKeyEq hij hk T)).val := by
  apply Subtype.ext
  exact trade_eq_of_key_eq hij hk T.val T.property.1
    (assignmentEquivOfKeyEq hij hk T).property.1

theorem stateFiberEquiv_symm_leftSet {n : Nat} {d : Fin n → Nat}
    {G H : GraphState n d} {i j : Fin n} (hij : i ≠ j)
    (hk : key i j H.val = key i j G.val) :
    ((stateFiberEquiv G i j hij).symm
      (stateFiberEquiv G i j hij ⟨H, hk⟩)).val = H := by
  exact congrArg Subtype.val ((stateFiberEquiv G i j hij).symm_apply_apply ⟨H, hk⟩)

theorem singletonSet_card_le (G : SimpleGraph V) (i j : V) :
    (singletonSet G i j).card ≤ Fintype.card V := Finset.card_le_univ _

theorem trade_leftSet_of_key_eq {G H : SimpleGraph V} {i j : V} (hij : i ≠ j)
    (hk : key i j G = key i j H)
    (hT : leftSet H i j ⊆ singletonSet G i j) :
    trade G i j hij (leftSet H i j) hT = H := by
  rw [trade_eq_of_key_eq hij hk _ hT (leftSet_subset_singletonSet H i j)]
  exact trade_original H i j hij

def assignmentEquivOfKeyCardEq {G H : SimpleGraph V} {i j : V}
    (hk : key i j G = key i j H)
    (hc : (leftSet G i j).card = (leftSet H i j).card) :
    Assignment G i j ≃ Assignment H i j where
  toFun T := ⟨T.val, by
    constructor
    · rw [← singletonSet_eq_of_key_eq hk]
      exact T.property.1
    · exact T.property.2.trans hc⟩
  invFun T := ⟨T.val, by
    constructor
    · rw [singletonSet_eq_of_key_eq hk]
      exact T.property.1
    · exact T.property.2.trans hc.symm⟩
  left_inv T := by apply Subtype.ext; rfl
  right_inv T := by apply Subtype.ext; rfl

@[simp] theorem assignmentEquivOfKeyCardEq_val {G H : SimpleGraph V} {i j : V}
    (hk : key i j G = key i j H)
    (hc : (leftSet G i j).card = (leftSet H i j).card)
    (T : Assignment G i j) : (assignmentEquivOfKeyCardEq hk hc T).val = T.val := rfl

def stateAssignmentEquiv {n : Nat} {d : Fin n → Nat}
    (G H : GraphState n d) {i j : Fin n} (hij : i ≠ j)
    (hk : key i j G.val = key i j H.val) :
    Assignment G.val i j ≃ Assignment H.val i j :=
  assignmentEquivOfKeyEq hij hk

@[simp] theorem stateAssignmentEquiv_val {n : Nat} {d : Fin n → Nat}
    (G H : GraphState n d) {i j : Fin n} (hij : i ≠ j)
    (hk : key i j G.val = key i j H.val) (T : Assignment G.val i j) :
    (stateAssignmentEquiv G H hij hk T).val = T.val := rfl

theorem stateFiberEquiv_symm_val_eq {n : Nat} {d : Fin n → Nat}
    (G H : GraphState n d) {i j : Fin n} (hij : i ≠ j)
    (hk : key i j G.val = key i j H.val) (T : Assignment G.val i j) :
    ((stateFiberEquiv G i j hij).symm T).val =
      ((stateFiberEquiv H i j hij).symm (stateAssignmentEquiv G H hij hk T)).val :=
  stateFiberEquiv_symm_eq_of_key_eq hij hk T

end Problem315.PairFiber

end

end OAI
