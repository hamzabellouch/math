import OAI.Probability.SwitchChain.PairFiberDegree

namespace OAI

noncomputable section

namespace Problem315.PairFiber

variable {V : Type*} [Fintype V]

abbrev Assignment (G : SimpleGraph V) (i j : V) :=
  {T : Finset V // T ⊆ singletonSet G i j ∧ T.card = (leftSet G i j).card}

abbrev GraphFiber (G : SimpleGraph V) (i j : V) :=
  {H : SimpleGraph V // key i j H = key i j G ∧
    (leftSet H i j).card = (leftSet G i j).card}

theorem trade_original (G : SimpleGraph V) (i j : V) (hij : i ≠ j) :
    trade G i j hij (leftSet G i j) (leftSet_subset_singletonSet G i j) = G := by
  apply graph_eq_of_key_leftSet_eq
  · exact key_trade _ _ _ _ _ _
  · exact leftSet_trade _ _ _ _ _ _

def graphFiberEquiv (G : SimpleGraph V) (i j : V) (hij : i ≠ j) :
    GraphFiber G i j ≃ Assignment G i j where
  toFun H := ⟨leftSet H.val i j, by
    constructor
    · rw [← singletonSet_eq_of_key_eq H.property.1]
      exact leftSet_subset_singletonSet H.val i j
    · exact H.property.2⟩
  invFun T := ⟨trade G i j hij T.val T.property.1, by
    constructor
    · exact key_trade _ _ _ _ _ _
    · rw [leftSet_trade]
      exact T.property.2⟩
  left_inv H := by
    have hsub : leftSet H.val i j ⊆ singletonSet G i j := by
      rw [← singletonSet_eq_of_key_eq H.property.1]
      exact leftSet_subset_singletonSet _ _ _
    apply Subtype.ext
    change trade G i j hij (leftSet H.val i j) hsub = H.val
    apply graph_eq_of_key_leftSet_eq
    · exact (key_trade G i j hij (leftSet H.val i j) hsub).trans H.property.1.symm
    · exact leftSet_trade G i j hij (leftSet H.val i j) hsub
  right_inv T := by
    apply Subtype.ext
    change leftSet (trade G i j hij T.val T.property.1) i j = T.val
    exact leftSet_trade G i j hij T.val T.property.1

@[simp] theorem graphFiberEquiv_apply (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (H : GraphFiber G i j) : (graphFiberEquiv G i j hij H).val = leftSet H.val i j := rfl

@[simp] theorem graphFiberEquiv_symm_apply (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Assignment G i j) :
    ((graphFiberEquiv G i j hij).symm T).val = trade G i j hij T.val T.property.1 := rfl

abbrev StateFiber {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) :=
  {H : GraphState n d // key i j H.val = key i j G.val}

def stateGraphFiberEquiv {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    StateFiber G i j ≃ GraphFiber G.val i j where
  toFun H := ⟨H.val.val, H.property,
    (leftSet_card_eq_iff_degree_eq hij H.property).mpr
      ((H.val.property i).trans (G.property i).symm)⟩
  invFun H := ⟨⟨H.val, fun v =>
      (degrees_eq_of_key_leftSet_card_eq hij H.property.1 H.property.2 v).trans
        (G.property v)⟩, H.property.1⟩
  left_inv H := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv H := by
    apply Subtype.ext
    rfl

def stateFiberEquiv {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    StateFiber G i j ≃ Assignment G.val i j :=
  (stateGraphFiberEquiv G i j hij).trans (graphFiberEquiv G.val i j hij)

@[simp] theorem stateFiberEquiv_apply {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) (H : StateFiber G i j) :
    (stateFiberEquiv G i j hij H).val = leftSet H.val.val i j := rfl

@[simp] theorem stateFiberEquiv_symm_apply {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) (T : Assignment G.val i j) :
    ((stateFiberEquiv G i j hij).symm T).val.val =
      trade G.val i j hij T.val T.property.1 := rfl

theorem assignment_natCard (G : SimpleGraph V) (i j : V) :
    Nat.card (Assignment G i j) =
      Nat.choose (singletonSet G i j).card (leftSet G i j).card := by
  classical
  let e : Assignment G i j ≃ ((singletonSet G i j).powersetCard (leftSet G i j).card) :=
    { toFun := fun T => ⟨T.val, Finset.mem_powersetCard.mpr T.property⟩
      invFun := fun T => ⟨T.val, Finset.mem_powersetCard.mp T.property⟩
      left_inv := fun T => by apply Subtype.ext; rfl
      right_inv := fun T => by apply Subtype.ext; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard]

theorem stateFiber_natCard {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    Nat.card (StateFiber G i j) =
      Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card := by
  rw [Nat.card_congr (stateFiberEquiv G i j hij)]
  exact assignment_natCard G.val i j

end Problem315.PairFiber

end

end OAI
