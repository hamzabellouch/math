import OAI.Probability.SwitchChain.TripleGraphEncoding
import OAI.Probability.SwitchChain.OrthogonalPairResampling

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.TripleInternalEncoding
attribute [local instance] Classical.propDecidable

theorem complement_edges_eq (G H : SimpleGraph (Fin 3)) (i : Fin 3)
    (he : internalEdgeCount G = internalEdgeCount H)
    (hd : graphDegree G i = graphDegree H i) :
    ∀ u v, u ≠ i → v ≠ i → (G.Adj u v ↔ H.Adj u v) := by
  unfold internalEdgeCount at he
  fin_cases i
  · change graphDegree G 0 = graphDegree H 0 at hd
    rw [degree_zero, degree_zero] at hd
    have h12 : G.Adj 1 2 ↔ H.Adj 1 2 := (edgeBit_eq_iff G H 1 2).mp (by omega)
    have h21 : G.Adj 2 1 ↔ H.Adj 2 1 :=
      (G.adj_comm 2 1).trans (h12.trans (H.adj_comm 1 2))
    intro u v hu hv
    fin_cases u <;> fin_cases v <;> simp_all
  · change graphDegree G 1 = graphDegree H 1 at hd
    rw [degree_one, degree_one] at hd
    have h02 : G.Adj 0 2 ↔ H.Adj 0 2 := (edgeBit_eq_iff G H 0 2).mp (by omega)
    have h20 : G.Adj 2 0 ↔ H.Adj 2 0 :=
      (G.adj_comm 2 0).trans (h02.trans (H.adj_comm 0 2))
    intro u v hu hv
    fin_cases u <;> fin_cases v <;> simp_all
  · change graphDegree G 2 = graphDegree H 2 at hd
    rw [degree_two, degree_two] at hd
    have h01 : G.Adj 0 1 ↔ H.Adj 0 1 := (edgeBit_eq_iff G H 0 1).mp (by omega)
    have h10 : G.Adj 1 0 ↔ H.Adj 1 0 :=
      (G.adj_comm 1 0).trans (h01.trans (H.adj_comm 0 1))
    intro u v hu hv
    fin_cases u <;> fin_cases v <;> simp_all

variable {W : Type*} [Fintype W]

def complementaryPair (i : Fin 3) : Finset (Fin 3 ⊕ W) := by
  classical
  exact (Finset.univ.image Sum.inl).erase (Sum.inl i)

omit [Fintype W] in
@[simp] theorem inl_mem_complementaryPair (i v : Fin 3) :
    (Sum.inl v : Fin 3 ⊕ W) ∈ complementaryPair i ↔ v ≠ i := by
  classical
  simp [complementaryPair]

omit [Fintype W] in
@[simp] theorem inr_notMem_complementaryPair (i : Fin 3) (w : W) :
    (Sum.inr w : Fin 3 ⊕ W) ∉ complementaryPair i := by
  classical
  simp [complementaryPair]

def SamePairRestrictions {V : Type*} (a : Finset V) (G H : SimpleGraph V) : Prop :=
  (∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v)

variable {O : SimpleGraph W} {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}

theorem adjacencyBit_eq_one {V : Type*} (G : SimpleGraph V) (u v : V) :
    adjacencyBit G u v = 1 ↔ G.Adj u v := by simp [adjacencyBit]

theorem samePairRestrictions_iff_row (G H : GraphTripleCell O e d c) (i : Fin 3) :
    SamePairRestrictions (complementaryPair i) G.val H.val ↔
      (graphToCell G).outside i = (graphToCell H).outside i := by
  classical
  constructor
  · intro h
    funext w
    have ha := h.1 (Sum.inl i) (by simp) (Sum.inr w) (by simp)
    simp only [graphToCell, adjacencyBit, ha]
  · intro hrow
    have hcross (w : W) : G.val.Adj (Sum.inl i) (Sum.inr w) ↔
        H.val.Adj (Sum.inl i) (Sum.inr w) := by
      have hb := congrFun hrow w
      exact (adjacencyBit_eq_one G.val _ _).symm.trans
        ((iff_of_eq (congrArg (fun x : ℕ => x = 1) hb)).trans
          (adjacencyBit_eq_one H.val _ _))
    have houtside (w z : W) : G.val.Adj (Sum.inr w) (Sum.inr z) ↔
        H.val.Adj (Sum.inr w) (Sum.inr z) := by
      have heq : outsideGraph G.val = outsideGraph H.val :=
        G.property.1.trans H.property.1.symm
      exact Iff.of_eq (congrArg (fun K : SimpleGraph W => K.Adj w z) heq)
    have hdegree : graphDegree (internalGraph G.val) i =
        graphDegree (internalGraph H.val) i := by
      have hG := (graphToCell G).rows i
      have hH := (graphToCell H).rows i
      rw [hrow] at hG
      exact Nat.add_left_cancel (hG.trans hH.symm)
    have hcomp := complement_edges_eq (internalGraph G.val) (internalGraph H.val) i
      (G.property.2.1.trans H.property.2.1.symm) hdegree
    constructor
    · intro u hu v hv
      cases u with
      | inl j =>
          have hji : j = i := by simpa using hu
          subst j
          cases v with
          | inl k =>
              have hki : k = i := by simpa using hv
              subst k
              simp
          | inr w => exact hcross w
      | inr w =>
          cases v with
          | inl j =>
              have hji : j = i := by simpa using hv
              subst j
              exact (G.val.adj_comm _ _).trans ((hcross w).trans (H.val.adj_comm _ _))
          | inr z => exact houtside w z
    · intro u hu v hv
      cases u with
      | inl j =>
          have hji : j ≠ i := by simpa using hu
          cases v with
          | inl k => exact hcomp j k hji (by simpa using hv)
          | inr w => simp at hv
      | inr w => simp at hu

theorem rightDegree_eq (G : GraphTripleCell O e d c) (w : W) :
    G.val.degree (Sum.inr w) = c w + O.degree w := by
  have hsum := G.val.degree_eq_sum_if_adj (R := ℕ) (Sum.inr w)
  simp only [Nat.cast_id, Fintype.sum_sum_type] at hsum
  rw [hsum]
  have hleft : (∑ v : Fin 3, if G.val.Adj (Sum.inr w) (Sum.inl v) then 1 else 0) =
      crossColumn G.val w := by
    unfold crossColumn adjacencyBit
    apply Finset.sum_congr rfl
    intro v hv
    rw [G.val.adj_comm (Sum.inr w) (Sum.inl v)]
  have hright : (∑ z : W, if G.val.Adj (Sum.inr w) (Sum.inr z) then 1 else 0) =
      O.degree w := by
    have ho := O.degree_eq_sum_if_adj (R := ℕ) w
    simp only [Nat.cast_id] at ho
    rw [ho]
    apply Finset.sum_congr rfl
    intro z hz
    have ha : G.val.Adj (Sum.inr w) (Sum.inr z) ↔ O.Adj w z :=
      Iff.of_eq (congrArg (fun K : SimpleGraph W => K.Adj w z) G.property.1)
    simp only [ha]
  rw [hleft, hright, G.property.2.2.2]

theorem graphCell_degrees_eq (G H : GraphTripleCell O e d c) :
    ∀ v, G.val.degree v = H.val.degree v := by
  intro v
  cases v with
  | inl i =>
      rw [← leftDegree_eq_degree, ← leftDegree_eq_degree]
      exact (G.property.2.2.1 i).trans (H.property.2.2.1 i).symm
  | inr w => rw [rightDegree_eq, rightDegree_eq]

def SamePairData {V : Type*} (a : Finset V) (G H : SimpleGraph V) : Prop :=
  (∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ w ∉ a, (a.filter (G.Adj w)).card = (a.filter (H.Adj w)).card)

theorem samePairData_iff_restrictions {V : Type*} [Fintype V]
    (a : Finset V) (G H : SimpleGraph V)
    (hdeg : ∀ w, G.degree w = H.degree w) :
    SamePairData a G H ↔ SamePairRestrictions a G H := by
  classical
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hout, hin⟩
    refine ⟨hout, hin, ?_⟩
    intro w hw
    have hsplit (K : SimpleGraph V) :
        K.degree w = (a.filter (K.Adj w)).card +
          ((Finset.univ.filter (K.Adj w)).filter (fun v => v ∉ a)).card := by
      have h := (Finset.univ.filter (K.Adj w)).card_filter_add_card_filter_not
        (fun v => v ∈ a)
      have hinset : (Finset.univ.filter (K.Adj w)).filter (fun v => v ∈ a) =
          a.filter (K.Adj w) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
      rw [hinset] at h
      have hcard : (Finset.univ.filter (K.Adj w)).card = K.degree w := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        exact (K.degree_eq_sum_if_adj (R := ℕ) w).symm
      rw [hcard] at h
      exact h.symm
    have hs : ((Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a)) =
        ((Finset.univ.filter (H.Adj w)).filter (fun v => v ∉ a)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hG, hv⟩
        exact ⟨(hout w hw v hv).mp hG, hv⟩
      · rintro ⟨hH, hv⟩
        exact ⟨(hout w hw v hv).mpr hH, hv⟩
    have h := hdeg w
    rw [hsplit G, hsplit H, hs] at h
    exact Nat.add_right_cancel h

theorem samePairData_iff_row (G H : GraphTripleCell O e d c) (i : Fin 3) :
    SamePairData (complementaryPair i) G.val H.val ↔
      (graphToCell G).outside i = (graphToCell H).outside i := by
  rw [samePairData_iff_restrictions _ _ _ (graphCell_degrees_eq G H),
    samePairRestrictions_iff_row]

theorem samePairData_iff_sameFiber {n : ℕ} (a : Finset (Fin n))
    (G H : SimpleGraph (Fin n)) :
    SamePairData a G H ↔ PairResampling.SameFiber a G H := Iff.rfl

theorem samePairData_iff_augmentedRow (G H : GraphTripleCell O e d c) (i : Fin 3) :
    SamePairData (complementaryPair i) G.val H.val ↔
      (encodeCell (graphToCell G)).matrix i = (encodeCell (graphToCell H)).matrix i := by
  exact (samePairData_iff_row G H i).trans
    (encode_row_eq_iff (graphToCell G) (graphToCell H) i).symm

theorem rightDegree_decompose (G : SimpleGraph (Fin 3 ⊕ W)) (w : W) :
    G.degree (Sum.inr w) = crossColumn G w + (outsideGraph G).degree w := by
  let A : GraphTripleCell (outsideGraph G) (internalEdgeCount (internalGraph G))
      (leftDegree G) (crossColumn G) := ⟨G, rfl, rfl, (fun _ => rfl), (fun _ => rfl)⟩
  exact rightDegree_eq A w

theorem edgeCount_eq_of_complement (G H : SimpleGraph (Fin 3)) (i : Fin 3)
    (hd : graphDegree G i = graphDegree H i)
    (ho : ∀ u v, u ≠ i → v ≠ i → (G.Adj u v ↔ H.Adj u v)) :
    internalEdgeCount G = internalEdgeCount H := by
  unfold internalEdgeCount
  fin_cases i
  · change graphDegree G 0 = graphDegree H 0 at hd
    rw [degree_zero, degree_zero] at hd
    have hb := (edgeBit_eq_iff G H 1 2).mpr (ho 1 2 (by decide) (by decide))
    omega
  · change graphDegree G 1 = graphDegree H 1 at hd
    rw [degree_one, degree_one] at hd
    have hb := (edgeBit_eq_iff G H 0 2).mpr (ho 0 2 (by decide) (by decide))
    omega
  · change graphDegree G 2 = graphDegree H 2 at hd
    rw [degree_two, degree_two] at hd
    have hb := (edgeBit_eq_iff G H 0 1).mpr (ho 0 1 (by decide) (by decide))
    omega

theorem cell_preserved_by_pair_data (G : GraphTripleCell O e d c)
    (H : SimpleGraph (Fin 3 ⊕ W)) (i : Fin 3)
    (hdeg : ∀ v, G.val.degree v = H.degree v)
    (hf : SamePairData (complementaryPair i) G.val H) :
    outsideGraph H = O ∧ internalEdgeCount (internalGraph H) = e ∧
      (∀ v, leftDegree H v = d v) ∧ ∀ w, crossColumn H w = c w := by
  classical
  have hout : outsideGraph G.val = outsideGraph H := by
    ext w z
    exact hf.1 (Sum.inr w) (by simp) (Sum.inr z) (by simp)
  have hrow : (fun w : W => adjacencyBit G.val (Sum.inl i) (Sum.inr w)) =
      (fun w : W => adjacencyBit H (Sum.inl i) (Sum.inr w)) := by
    funext w
    have ha := hf.1 (Sum.inl i) (by simp) (Sum.inr w) (by simp)
    simp only [adjacencyBit, ha]
  have hleft : ∀ v, leftDegree G.val v = leftDegree H v := by
    intro v
    rw [leftDegree_eq_degree, leftDegree_eq_degree]
    exact hdeg (Sum.inl v)
  have hdinternal : graphDegree (internalGraph G.val) i =
      graphDegree (internalGraph H) i := by
    have h := hleft i
    rw [leftDegree_decompose, leftDegree_decompose, hrow] at h
    exact Nat.add_right_cancel h
  have hecount : internalEdgeCount (internalGraph G.val) =
      internalEdgeCount (internalGraph H) := by
    apply edgeCount_eq_of_complement _ _ i hdinternal
    intro u v hu hv
    exact hf.2.1 (Sum.inl u) (by simpa using hu) (Sum.inl v) (by simpa using hv)
  refine ⟨hout.symm.trans G.property.1, hecount.symm.trans G.property.2.1, ?_, ?_⟩
  · intro v
    exact (hleft v).symm.trans (G.property.2.2.1 v)
  · intro w
    have h := hdeg (Sum.inr w)
    rw [rightDegree_decompose, rightDegree_decompose, hout] at h
    exact (Nat.add_right_cancel h).symm.trans (G.property.2.2.2 w)

end Problem315.TripleInternalEncoding

end

end OAI
