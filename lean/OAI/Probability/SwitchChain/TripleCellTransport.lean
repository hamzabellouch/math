import OAI.Probability.SwitchChain.TripleStateReindex
import OAI.Probability.SwitchChain.TriplePairFiber

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCellTransport

open TripleStateReindex TripleInternalEncoding
attribute [local instance] Classical.propDecidable

theorem degreeCount_eq_degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : degreeCount G v = G.degree v := by
  classical
  simp only [degreeCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact (G.degree_eq_sum_if_adj (R := ℕ) v).symm

variable {n : ℕ} {d : Fin n → ℕ}
variable (T : Finset (Fin n)) (hT : T.card = 3)

def splitGraph (G : GraphState n d) : SimpleGraph (Fin 3 ⊕ Outside T) :=
  G.val.comap (splitEquiv T hT)

theorem splitGraph_degree (G : GraphState n d) (v : Fin 3 ⊕ Outside T) :
    (splitGraph T hT G).degree v = d (splitEquiv T hT v) := by
  rw [← degreeCount_eq_degree]
  change degreeCount (G.val.comap (splitEquiv T hT)) v = _
  rw [degreeCount_comap]
  exact G.property _

abbrev Cell (G : GraphState n d) :=
  {H : GraphState n d //
    outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) ∧
    internalEdgeCount (internalGraph (splitGraph T hT H)) =
      internalEdgeCount (internalGraph (splitGraph T hT G)) ∧
    ∀ w, crossColumn (splitGraph T hT H) w = crossColumn (splitGraph T hT G) w}

abbrev Model (G : GraphState n d) :=
  GraphTripleCell (outsideGraph (splitGraph T hT G))
    (internalEdgeCount (internalGraph (splitGraph T hT G)))
    (leftDegree (splitGraph T hT G)) (crossColumn (splitGraph T hT G))

def referenceModel (G : GraphState n d) : Model T hT G :=
  ⟨splitGraph T hT G, rfl, rfl, (fun _ => rfl), (fun _ => rfl)⟩

def toModel (G : GraphState n d) (H : Cell T hT G) : Model T hT G :=
  ⟨splitGraph T hT H.val, H.property.1, H.property.2.1, by
    intro v
    rw [leftDegree_eq_degree, leftDegree_eq_degree, splitGraph_degree,
      splitGraph_degree], H.property.2.2⟩

def modelState (G : GraphState n d) (H : Model T hT G) : GraphState n d :=
  (stateEquiv T hT d).symm ⟨H.val, by
    intro v
    rw [degreeCount_eq_degree,
      graphCell_degrees_eq H (referenceModel T hT G) v]
    exact splitGraph_degree T hT G v⟩

@[simp] theorem splitGraph_modelState (G : GraphState n d) (H : Model T hT G) :
    splitGraph T hT (modelState T hT G H) = H.val := by
  change ((stateEquiv T hT d) ((stateEquiv T hT d).symm _)).val = H.val
  simp only [Equiv.apply_symm_apply]

def fromModel (G : GraphState n d) (H : Model T hT G) : Cell T hT G :=
  ⟨modelState T hT G H, by
    rw [splitGraph_modelState]
    exact ⟨H.property.1, H.property.2.1, H.property.2.2.2⟩⟩

def cellEquiv (G : GraphState n d) : Cell T hT G ≃ Model T hT G where
  toFun := toModel T hT G
  invFun := fromModel T hT G
  left_inv H := by
    apply Subtype.ext
    apply (stateEquiv T hT d).injective
    apply Subtype.ext
    exact splitGraph_modelState T hT G (toModel T hT G H)
  right_inv H := by
    apply Subtype.ext
    exact splitGraph_modelState T hT G H

def referenceCell (G : GraphState n d) : Cell T hT G :=
  ⟨G, rfl, rfl, fun _ => rfl⟩

def matrixEquiv (G : GraphState n d) : Cell T hT G ≃
    AugmentedMatrix (Outside T)
      (internalEdgeCount (internalGraph (splitGraph T hT G)))
      (leftDegree (splitGraph T hT G)) (crossColumn (splitGraph T hT G)) :=
  (cellEquiv T hT G).trans (graphTripleMatrixEquiv _ _
    (internalEdgeCount_le_three _) _ _
    (rowOffset_le_of_nonempty ⟨graphToCell (referenceModel T hT G)⟩))

def pair (i : Fin 3) : Finset (Fin n) :=
  (complementaryPair (W := Outside T) i).map (splitEquiv T hT).toEmbedding

@[simp] theorem split_mem_pair (i : Fin 3) (v : Fin 3 ⊕ Outside T) :
    splitEquiv T hT v ∈ pair T hT i ↔ v ∈ complementaryPair i := by
  classical
  simp [pair]

theorem pair_eq_erase (i : Fin 3) :
    pair T hT i = T.erase (splitEquiv T hT (Sum.inl i)) := by
  classical
  ext v
  obtain ⟨x, rfl⟩ := (splitEquiv T hT).surjective v
  rw [split_mem_pair]
  cases x with
  | inl j =>
      simp only [inl_mem_complementaryPair, Finset.mem_erase,
        splitEquiv_inl_mem, and_true]
      constructor
      · intro h heq
        exact h (Sum.inl.inj ((splitEquiv T hT).injective heq))
      · intro h heq
        exact h (congrArg (fun j => splitEquiv T hT (Sum.inl j)) heq)
  | inr w =>
      simp only [inr_notMem_complementaryPair, Finset.mem_erase,
        splitEquiv_inr_not_mem, and_false]

theorem restrictions_map_iff {V W : Type*} (e : V ≃ W) (a : Finset V)
    (G H : SimpleGraph W) :
    SamePairRestrictions (a.map e.toEmbedding) G H ↔
      SamePairRestrictions a (G.comap e) (H.comap e) := by
  classical
  constructor
  · rintro ⟨hout, hin⟩
    constructor
    · intro u hu v hv
      exact hout (e u) (by simpa using hu) (e v) (by simpa using hv)
    · intro u hu v hv
      exact hin (e u) (by simpa using hu) (e v) (by simpa using hv)
  · rintro ⟨hout, hin⟩
    constructor
    · intro u hu v hv
      obtain ⟨x, rfl⟩ := e.surjective u
      obtain ⟨y, rfl⟩ := e.surjective v
      exact hout x (by simpa using hu) y (by simpa using hv)
    · intro u hu v hv
      obtain ⟨x, rfl⟩ := e.surjective u
      obtain ⟨y, rfl⟩ := e.surjective v
      exact hin x (by simpa using hu) y (by simpa using hv)

theorem sameFiber_iff_splitPairData (G H : GraphState n d) (i : Fin 3) :
    PairResampling.SameFiber (pair T hT i) G.val H.val ↔
      SamePairData (complementaryPair i) (splitGraph T hT G) (splitGraph T hT H) := by
  rw [PairResampling.sameFiber_state_iff]
  rw [samePairData_iff_restrictions _ _ _ (by
    intro v
    rw [splitGraph_degree, splitGraph_degree])]
  exact restrictions_map_iff (splitEquiv T hT) _ G.val H.val

theorem cell_of_sameFiber (G H : GraphState n d) (i : Fin 3)
    (hf : PairResampling.SameFiber (pair T hT i) G.val H.val) :
    outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) ∧
    internalEdgeCount (internalGraph (splitGraph T hT H)) =
      internalEdgeCount (internalGraph (splitGraph T hT G)) ∧
    ∀ w, crossColumn (splitGraph T hT H) w = crossColumn (splitGraph T hT G) w := by
  have h := cell_preserved_by_pair_data (referenceModel T hT G)
    (splitGraph T hT H) i (by
      intro v
      exact (splitGraph_degree T hT G v).trans (splitGraph_degree T hT H v).symm)
    ((sameFiber_iff_splitPairData T hT G H i).mp hf)
  exact ⟨h.1, h.2.1, h.2.2.2⟩

theorem sameFiber_iff_matrixRow (G : GraphState n d)
    (H K : Cell T hT G) (i : Fin 3) :
    PairResampling.SameFiber (pair T hT i) H.val.val K.val.val ↔
      (matrixEquiv T hT G H).matrix i = (matrixEquiv T hT G K).matrix i := by
  rw [sameFiber_iff_splitPairData]
  exact samePairData_iff_augmentedRow (toModel T hT G H) (toModel T hT G K) i

theorem cell_of_sameFiber_of_cell (G : GraphState n d) (H : Cell T hT G)
    (K : GraphState n d) (i : Fin 3)
    (hf : PairResampling.SameFiber (pair T hT i) H.val.val K.val) :
    outsideGraph (splitGraph T hT K) = outsideGraph (splitGraph T hT G) ∧
    internalEdgeCount (internalGraph (splitGraph T hT K)) =
      internalEdgeCount (internalGraph (splitGraph T hT G)) ∧
    ∀ w, crossColumn (splitGraph T hT K) w = crossColumn (splitGraph T hT G) w := by
  have h := cell_of_sameFiber T hT H.val K i hf
  exact ⟨h.1.trans H.property.1, h.2.1.trans H.property.2.1,
    fun w => (h.2.2 w).trans (H.property.2.2 w)⟩

theorem pair_card (i : Fin 3) : (pair T hT i).card = 2 := by
  rw [pair_eq_erase, Finset.card_erase_of_mem (splitEquiv_inl_mem T hT i), hT]

theorem pair_mem_powersetCard (i : Fin 3) : pair T hT i ∈ T.powersetCard 2 := by
  rw [Finset.mem_powersetCard]
  exact ⟨by rw [pair_eq_erase]; exact Finset.erase_subset _ _, pair_card T hT i⟩

theorem pair_injective : Function.Injective (pair T hT) := by
  intro i j heq
  by_contra hij
  have hi : splitEquiv T hT (Sum.inl i) ∈ pair T hT j := by
    rw [split_mem_pair]
    exact (inl_mem_complementaryPair j i).mpr hij
  rw [← heq, split_mem_pair] at hi
  simp at hi

def pairEquiv : Fin 3 ≃ T.powersetCard 2 := by
  let f : Fin 3 → T.powersetCard 2 := fun i => ⟨pair T hT i, pair_mem_powersetCard T hT i⟩
  apply Equiv.ofBijective f
  have hinj : Function.Injective f := by
    intro i j h
    exact pair_injective T hT (congrArg Subtype.val h)
  refine ⟨hinj, ?_⟩
  have hc : Fintype.card (Fin 3) = Fintype.card (T.powersetCard 2) := by
    rw [Fintype.card_coe, Finset.card_powersetCard, hT]
    rfl
  exact (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hc⟩ |>.2

theorem sum_pair {E : Type*} [AddCommMonoid E] (f : Finset (Fin n) → E) :
    ∑ i : Fin 3, f (pair T hT i) = ∑ a ∈ T.powersetCard 2, f a := by
  change (∑ i : Fin 3, (fun a : T.powersetCard 2 => f a.val) (pairEquiv T hT i)) = _
  exact ((pairEquiv T hT).sum_comp (fun a => f a.val)).trans
    (Finset.sum_coe_sort _ _)

theorem sum_leftDegree_decompose {W : Type*} [Fintype W]
    (G : SimpleGraph (Fin 3 ⊕ W)) :
    (∑ i, leftDegree G i) = 2 * internalEdgeCount (internalGraph G) +
      ∑ w, crossColumn G w := by
  simp_rw [leftDegree_decompose]
  rw [Finset.sum_add_distrib, sum_degrees, Finset.sum_comm]
  rfl

theorem cellData_iff_outsideGraph (G H : GraphState n d) :
    (outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) ∧
      internalEdgeCount (internalGraph (splitGraph T hT H)) =
        internalEdgeCount (internalGraph (splitGraph T hT G)) ∧
      ∀ w, crossColumn (splitGraph T hT H) w = crossColumn (splitGraph T hT G) w) ↔
    outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) := by
  refine ⟨And.left, fun ho => ?_⟩
  have hc : ∀ w, crossColumn (splitGraph T hT H) w =
      crossColumn (splitGraph T hT G) w := by
    intro w
    have hd := (splitGraph_degree T hT H (Sum.inr w)).trans
      (splitGraph_degree T hT G (Sum.inr w)).symm
    rw [rightDegree_decompose, rightDegree_decompose, ho] at hd
    exact Nat.add_right_cancel hd
  have hl : ∀ i, leftDegree (splitGraph T hT H) i =
      leftDegree (splitGraph T hT G) i := by
    intro i
    rw [leftDegree_eq_degree, leftDegree_eq_degree,
      splitGraph_degree, splitGraph_degree]
  have hs : (∑ i, leftDegree (splitGraph T hT H) i) =
      ∑ i, leftDegree (splitGraph T hT G) i := Finset.sum_congr rfl (fun i _ => hl i)
  rw [sum_leftDegree_decompose, sum_leftDegree_decompose] at hs
  simp_rw [hc] at hs
  exact ⟨ho, by omega, hc⟩

theorem outsideGraph_eq_iff (G H : GraphState n d) :
    outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) ↔
      ∀ u ∉ T, ∀ v ∉ T, H.val.Adj u v ↔ G.val.Adj u v := by
  constructor
  · intro h u hu v hv
    exact Iff.of_eq (congrArg (fun K : SimpleGraph (Outside T) =>
      K.Adj ⟨u, hu⟩ ⟨v, hv⟩) h)
  · intro h
    ext u v
    exact h u.val u.property v.val v.property

def outsideCellEquiv (G : GraphState n d) :
    {H : GraphState n d //
      outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G)} ≃
      Cell T hT G where
  toFun H := ⟨H.val, (cellData_iff_outsideGraph T hT G H.val).mpr H.property⟩
  invFun H := ⟨H.val, H.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Problem315.TripleCellTransport

end

end OAI
