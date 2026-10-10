import OAI.Probability.SwitchChain.Definitions

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315.TripleEncoding

attribute [local instance] Classical.propDecidable

lemma graphDegree_three (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v =
      (if G.Adj v 0 then 1 else 0) +
      (if G.Adj v 1 then 1 else 0) +
      (if G.Adj v 2 then 1 else 0) := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fin.sum_univ_three]

lemma graphDegree_injective_three :
    Function.Injective (fun G : SimpleGraph (Fin 3) => graphDegree G) := by
  classical
  intro G H h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [graphDegree_three] at h0 h1 h2
  have hsG01 : G.Adj 1 0 ↔ G.Adj 0 1 := G.adj_comm _ _
  have hsG02 : G.Adj 2 0 ↔ G.Adj 0 2 := G.adj_comm _ _
  have hsG12 : G.Adj 2 1 ↔ G.Adj 1 2 := G.adj_comm _ _
  have hsH01 : H.Adj 1 0 ↔ H.Adj 0 1 := H.adj_comm _ _
  have hsH02 : H.Adj 2 0 ↔ H.Adj 0 2 := H.adj_comm _ _
  have hsH12 : H.Adj 2 1 ↔ H.Adj 1 2 := H.adj_comm _ _
  by_cases hg01 : G.Adj 0 1 <;>
    by_cases hg02 : G.Adj 0 2 <;>
    by_cases hg12 : G.Adj 1 2 <;>
    by_cases hh01 : H.Adj 0 1 <;>
    by_cases hh02 : H.Adj 0 2 <;>
    by_cases hh12 : H.Adj 1 2
  all_goals simp_all
  all_goals
    ext v w
    fin_cases v <;> fin_cases w <;>
      simp_all

def edgeCount (G : SimpleGraph (Fin 3)) : Nat :=
  (if G.Adj 0 1 then 1 else 0) + (if G.Adj 0 2 then 1 else 0) +
  (if G.Adj 1 2 then 1 else 0)

def missingVertexGraph (m : Fin 3) : SimpleGraph (Fin 3) where
  Adj u v := u ≠ v ∧ u ≠ m ∧ v ≠ m
  symm := by
    constructor
    intro u v h
    exact ⟨Ne.symm h.1, h.2.2, h.2.1⟩
  loopless := by
    constructor
    intro v h
    exact h.1 rfl

def centerGraph (c : Fin 3) : SimpleGraph (Fin 3) where
  Adj u v := u ≠ v ∧ (u = c ∨ v = c)
  symm := by
    constructor
    intro u v h
    exact ⟨Ne.symm h.1, h.2.symm⟩
  loopless := by
    constructor
    intro v h
    exact h.1 rfl

@[simp] lemma graphDegree_missingVertexGraph (m v : Fin 3) :
    graphDegree (missingVertexGraph m) v = if v = m then 0 else 1 := by
  fin_cases m <;> fin_cases v <;>
    simp only [graphDegree_three, missingVertexGraph] <;> split_ifs <;> omega

@[simp] lemma graphDegree_centerGraph (c v : Fin 3) :
    graphDegree (centerGraph c) v = if v = c then 2 else 1 := by
  fin_cases c <;> fin_cases v <;>
    simp only [graphDegree_three, centerGraph, true_or, and_true] <;> split_ifs <;> omega

@[simp] lemma edgeCount_missingVertexGraph (m : Fin 3) :
    edgeCount (missingVertexGraph m) = 1 := by
  fin_cases m <;> norm_num [edgeCount, missingVertexGraph]

@[simp] lemma edgeCount_centerGraph (c : Fin 3) :
    edgeCount (centerGraph c) = 2 := by
  fin_cases c <;> norm_num [edgeCount, centerGraph]

lemma missingVertexGraph_injective : Function.Injective missingVertexGraph := by
  intro m k h
  have hm := congrArg (fun G => graphDegree G m) h
  simp only [graphDegree_missingVertexGraph, ite_true] at hm
  split_ifs at hm with hmk
  exact hmk

lemma centerGraph_injective : Function.Injective centerGraph := by
  intro c k h
  have hc := congrArg (fun G => graphDegree G c) h
  simp only [graphDegree_centerGraph, ite_true] at hc
  split_ifs at hc with hck
  · exact hck
  · contradiction

lemma exists_missingVertexGraph_of_edgeCount_one (G : SimpleGraph (Fin 3))
    (he : edgeCount G = 1) : ∃ m : Fin 3, G = missingVertexGraph m := by
  have hs01 := G.adj_comm 1 0
  have hs02 := G.adj_comm 2 0
  have hs12 := G.adj_comm 2 1
  by_cases h01 : G.Adj 0 1 <;> by_cases h02 : G.Adj 0 2 <;>
    by_cases h12 : G.Adj 1 2
  all_goals simp_all [edgeCount]
  · refine ⟨2, ?_⟩
    ext u v
    fin_cases u <;> fin_cases v <;> simp_all [missingVertexGraph]
  · refine ⟨1, ?_⟩
    ext u v
    fin_cases u <;> fin_cases v <;> simp_all [missingVertexGraph]
  · refine ⟨0, ?_⟩
    ext u v
    fin_cases u <;> fin_cases v <;> simp_all [missingVertexGraph]

lemma exists_centerGraph_of_edgeCount_two (G : SimpleGraph (Fin 3))
    (he : edgeCount G = 2) : ∃ c : Fin 3, G = centerGraph c := by
  have hs01 := G.adj_comm 1 0
  have hs02 := G.adj_comm 2 0
  have hs12 := G.adj_comm 2 1
  by_cases h01 : G.Adj 0 1 <;> by_cases h02 : G.Adj 0 2 <;>
    by_cases h12 : G.Adj 1 2
  all_goals simp_all [edgeCount]
  · refine ⟨0, ?_⟩
    ext u v
    fin_cases u <;> fin_cases v <;> simp_all [centerGraph]
  · refine ⟨1, ?_⟩
    ext u v
    fin_cases u <;> fin_cases v <;> simp_all [centerGraph]
  · refine ⟨2, ?_⟩
    ext u v
    fin_cases u <;> fin_cases v <;> simp_all [centerGraph]

def oneEdgeEquiv : {G : SimpleGraph (Fin 3) // edgeCount G = 1} ≃ Fin 3 :=
  (Equiv.ofBijective
    (fun m : Fin 3 => (⟨missingVertexGraph m, edgeCount_missingVertexGraph m⟩ :
      {G : SimpleGraph (Fin 3) // edgeCount G = 1})) (by
      constructor
      · intro m k h
        exact missingVertexGraph_injective (congrArg Subtype.val h)
      · intro G
        obtain ⟨m, hm⟩ := exists_missingVertexGraph_of_edgeCount_one G.val G.property
        exact ⟨m, Subtype.ext hm.symm⟩)).symm

def twoEdgeEquiv : {G : SimpleGraph (Fin 3) // edgeCount G = 2} ≃ Fin 3 :=
  (Equiv.ofBijective
    (fun c : Fin 3 => (⟨centerGraph c, edgeCount_centerGraph c⟩ :
      {G : SimpleGraph (Fin 3) // edgeCount G = 2})) (by
      constructor
      · intro c k h
        exact centerGraph_injective (congrArg Subtype.val h)
      · intro G
        obtain ⟨c, hc⟩ := exists_centerGraph_of_edgeCount_two G.val G.property
        exact ⟨c, Subtype.ext hc.symm⟩)).symm

abbrev BinaryColumn (k : Nat) :=
  {x : Fin 3 → Fin 2 // ∑ v, (x v).val = k}

def omittedColumn (m : Fin 3) : Fin 3 → Fin 2 :=
  fun v => if v = m then 0 else 1

def markedColumn (c : Fin 3) : Fin 3 → Fin 2 :=
  fun v => if v = c then 1 else 0

lemma sum_omittedColumn (m : Fin 3) : ∑ v, (omittedColumn m v).val = 2 := by
  simp only [omittedColumn, apply_ite, Fin.val_zero, Fin.val_one]
  have hsum : (∑ x : Fin 3, if x = m then 0 else 1) +
      (∑ x : Fin 3, if x = m then 1 else 0) = (3 : Nat) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x : Fin 3, ((if x = m then 0 else 1) + (if x = m then 1 else 0)))
          = ∑ _x : Fin 3, (1 : Nat) := by
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> rfl
      _ = 3 := by simp
  have hm : (∑ x : Fin 3, if x = m then 1 else 0) = (1 : Nat) := by simp
  omega

lemma sum_markedColumn (c : Fin 3) : ∑ v, (markedColumn c v).val = 1 := by
  simp [markedColumn, apply_ite]

lemma omittedColumn_injective : Function.Injective omittedColumn := by
  intro m k h
  have hm := congrFun h m
  by_contra hmk
  simp [omittedColumn, hmk] at hm

lemma markedColumn_injective : Function.Injective markedColumn := by
  intro c k h
  have hc := congrFun h c
  by_contra hck
  simp [markedColumn, hck] at hc

lemma exists_omittedColumn (x : BinaryColumn 2) : ∃ m, x.val = omittedColumn m := by
  have hsum := x.property
  rw [Fin.sum_univ_three] at hsum
  have h0 := (x.val 0).isLt
  have h1 := (x.val 1).isLt
  have h2 := (x.val 2).isLt
  by_cases hz0 : (x.val 0).val = 0
  · have hv1 : (x.val 1).val = 1 := by omega
    have hv2 : (x.val 2).val = 1 := by omega
    refine ⟨0, ?_⟩
    funext v
    apply Fin.ext
    fin_cases v <;> simp only [omittedColumn] <;> split_ifs <;> simp_all
  · by_cases hz1 : (x.val 1).val = 0
    · have hv0 : (x.val 0).val = 1 := by omega
      have hv2 : (x.val 2).val = 1 := by omega
      refine ⟨1, ?_⟩
      funext v
      apply Fin.ext
      fin_cases v <;> simp only [omittedColumn] <;> split_ifs <;> simp_all
    · have hv0 : (x.val 0).val = 1 := by omega
      have hv1 : (x.val 1).val = 1 := by omega
      have hv2 : (x.val 2).val = 0 := by omega
      refine ⟨2, ?_⟩
      funext v
      apply Fin.ext
      fin_cases v <;> simp only [omittedColumn] <;> split_ifs <;> simp_all

lemma exists_markedColumn (x : BinaryColumn 1) : ∃ c, x.val = markedColumn c := by
  have hsum := x.property
  rw [Fin.sum_univ_three] at hsum
  have h0 := (x.val 0).isLt
  have h1 := (x.val 1).isLt
  have h2 := (x.val 2).isLt
  by_cases ho0 : (x.val 0).val = 1
  · have hv1 : (x.val 1).val = 0 := by omega
    have hv2 : (x.val 2).val = 0 := by omega
    refine ⟨0, ?_⟩
    funext v
    apply Fin.ext
    fin_cases v <;> simp only [markedColumn] <;> split_ifs <;> simp_all
  · by_cases ho1 : (x.val 1).val = 1
    · have hv0 : (x.val 0).val = 0 := by omega
      have hv2 : (x.val 2).val = 0 := by omega
      refine ⟨1, ?_⟩
      funext v
      apply Fin.ext
      fin_cases v <;> simp only [markedColumn] <;> split_ifs <;> simp_all
    · have hv0 : (x.val 0).val = 0 := by omega
      have hv1 : (x.val 1).val = 0 := by omega
      have hv2 : (x.val 2).val = 1 := by omega
      refine ⟨2, ?_⟩
      funext v
      apply Fin.ext
      fin_cases v <;> simp only [markedColumn] <;> split_ifs <;> simp_all

def omittedColumnEquiv : Fin 3 ≃ BinaryColumn 2 :=
  Equiv.ofBijective (fun m => ⟨omittedColumn m, sum_omittedColumn m⟩) (by
    constructor
    · intro m k h
      exact omittedColumn_injective (congrArg Subtype.val h)
    · intro x
      obtain ⟨m, hm⟩ := exists_omittedColumn x
      exact ⟨m, Subtype.ext hm.symm⟩)

def markedColumnEquiv : Fin 3 ≃ BinaryColumn 1 :=
  Equiv.ofBijective (fun c => ⟨markedColumn c, sum_markedColumn c⟩) (by
    constructor
    · intro c k h
      exact markedColumn_injective (congrArg Subtype.val h)
    · intro x
      obtain ⟨c, hc⟩ := exists_markedColumn x
      exact ⟨c, Subtype.ext hc.symm⟩)

def oneEdgeColumnEquiv :
    {G : SimpleGraph (Fin 3) // edgeCount G = 1} ≃ BinaryColumn 2 :=
  oneEdgeEquiv.trans omittedColumnEquiv

def twoEdgeColumnEquiv :
    {G : SimpleGraph (Fin 3) // edgeCount G = 2} ≃ BinaryColumn 1 :=
  twoEdgeEquiv.trans markedColumnEquiv

lemma oneEdgeEquiv_graph (G : {G : SimpleGraph (Fin 3) // edgeCount G = 1}) :
    missingVertexGraph (oneEdgeEquiv G) = G.val := by
  exact congrArg Subtype.val (oneEdgeEquiv.symm_apply_apply G)

lemma twoEdgeEquiv_graph (G : {G : SimpleGraph (Fin 3) // edgeCount G = 2}) :
    centerGraph (twoEdgeEquiv G) = G.val := by
  exact congrArg Subtype.val (twoEdgeEquiv.symm_apply_apply G)

lemma oneEdgeColumnEquiv_value
    (G : {G : SimpleGraph (Fin 3) // edgeCount G = 1}) (v : Fin 3) :
    ((oneEdgeColumnEquiv G).val v).val = graphDegree G.val v := by
  rw [← oneEdgeEquiv_graph G, graphDegree_missingVertexGraph]
  change (omittedColumn (oneEdgeEquiv G) v).val = _
  by_cases hv : v = oneEdgeEquiv G <;> simp [omittedColumn, hv]

lemma twoEdgeColumnEquiv_value
    (G : {G : SimpleGraph (Fin 3) // edgeCount G = 2}) (v : Fin 3) :
    ((twoEdgeColumnEquiv G).val v).val = graphDegree G.val v - 1 := by
  rw [← twoEdgeEquiv_graph G, graphDegree_centerGraph]
  change (markedColumn (twoEdgeEquiv G) v).val = _
  by_cases hv : v = twoEdgeEquiv G <;> simp [markedColumn, hv]

lemma twoEdgeColumnEquiv_degree
    (G : {G : SimpleGraph (Fin 3) // edgeCount G = 2}) (v : Fin 3) :
    graphDegree G.val v = ((twoEdgeColumnEquiv G).val v).val + 1 := by
  rw [← twoEdgeEquiv_graph G, graphDegree_centerGraph]
  change _ = (markedColumn (twoEdgeEquiv G) v).val + 1
  by_cases hv : v = twoEdgeEquiv G <;> simp [markedColumn, hv]

lemma edgeCount_le_three (G : SimpleGraph (Fin 3)) : edgeCount G ≤ 3 := by
  unfold edgeCount
  split_ifs <;> omega

lemma sum_graphDegree_eq (G : SimpleGraph (Fin 3)) :
    (∑ v, graphDegree G v) = 2 * edgeCount G := by
  simp only [Fin.sum_univ_three, graphDegree_three, edgeCount,
    G.irrefl, ite_false, zero_add, add_zero, G.adj_comm 1 0,
    G.adj_comm 2 0, G.adj_comm 2 1]
  ring

lemma eq_bot_of_edgeCount_zero (G : SimpleGraph (Fin 3)) (he : edgeCount G = 0) :
    G = ⊥ := by
  have hs01 := G.adj_comm 1 0
  have hs02 := G.adj_comm 2 0
  have hs12 := G.adj_comm 2 1
  by_cases h01 : G.Adj 0 1 <;> by_cases h02 : G.Adj 0 2 <;>
    by_cases h12 : G.Adj 1 2
  all_goals simp_all [edgeCount]
  ext u v
  fin_cases u <;> fin_cases v <;> simp_all

lemma eq_top_of_edgeCount_three (G : SimpleGraph (Fin 3)) (he : edgeCount G = 3) :
    G = ⊤ := by
  have hs01 := G.adj_comm 1 0
  have hs02 := G.adj_comm 2 0
  have hs12 := G.adj_comm 2 1
  by_cases h01 : G.Adj 0 1 <;> by_cases h02 : G.Adj 0 2 <;>
    by_cases h12 : G.Adj 1 2
  all_goals simp_all [edgeCount]
  ext u v
  fin_cases u <;> fin_cases v <;> simp_all

lemma graphDegree_of_edgeCount_zero (G : SimpleGraph (Fin 3))
    (he : edgeCount G = 0) (v : Fin 3) : graphDegree G v = 0 := by
  rw [eq_bot_of_edgeCount_zero G he]
  simp [graphDegree]

lemma graphDegree_of_edgeCount_three (G : SimpleGraph (Fin 3))
    (he : edgeCount G = 3) (v : Fin 3) : graphDegree G v = 2 := by
  rw [eq_top_of_edgeCount_three G he]
  fin_cases v <;> simp only [graphDegree_three, SimpleGraph.top_adj] <;>
    split_ifs <;> omega

end Problem315.TripleEncoding

end

end OAI
