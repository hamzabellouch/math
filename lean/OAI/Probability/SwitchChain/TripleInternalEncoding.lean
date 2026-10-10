import OAI.Probability.SwitchChain.Definitions

namespace OAI

noncomputable section
namespace Problem315.TripleInternalEncoding
attribute [local instance] Classical.propDecidable

def edgeBit (G : SimpleGraph (Fin 3)) (u v : Fin 3) : ℕ :=
  if G.Adj u v then 1 else 0

def internalEdgeCount (G : SimpleGraph (Fin 3)) : ℕ :=
  edgeBit G 0 1 + edgeBit G 0 2 + edgeBit G 1 2

theorem degree_zero (G : SimpleGraph (Fin 3)) :
    graphDegree G 0 = edgeBit G 0 1 + edgeBit G 0 2 := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  simp [edgeBit]

theorem degree_one (G : SimpleGraph (Fin 3)) :
    graphDegree G 1 = edgeBit G 0 1 + edgeBit G 1 2 := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  simp [edgeBit, G.adj_comm]

theorem degree_two (G : SimpleGraph (Fin 3)) :
    graphDegree G 2 = edgeBit G 0 2 + edgeBit G 1 2 := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  simp [edgeBit, G.adj_comm]

theorem edgeBit_le_one (G : SimpleGraph (Fin 3)) (u v : Fin 3) :
    edgeBit G u v ≤ 1 := by
  unfold edgeBit
  split <;> omega

theorem edgeBit_eq_iff (G H : SimpleGraph (Fin 3)) (u v : Fin 3) :
    edgeBit G u v = edgeBit H u v ↔ (G.Adj u v ↔ H.Adj u v) := by
  by_cases hg : G.Adj u v <;> by_cases hh : H.Adj u v <;> simp [edgeBit, hg, hh]

theorem degree_injective : Function.Injective
    (fun G : SimpleGraph (Fin 3) => graphDegree G) := by
  intro G H h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  change graphDegree G 0 = graphDegree H 0 at h0
  change graphDegree G 1 = graphDegree H 1 at h1
  change graphDegree G 2 = graphDegree H 2 at h2
  rw [degree_zero, degree_zero] at h0
  rw [degree_one, degree_one] at h1
  rw [degree_two, degree_two] at h2
  have h01 : G.Adj 0 1 ↔ H.Adj 0 1 :=
    (edgeBit_eq_iff G H 0 1).mp (by omega)
  have h02 : G.Adj 0 2 ↔ H.Adj 0 2 :=
    (edgeBit_eq_iff G H 0 2).mp (by omega)
  have h12 : G.Adj 1 2 ↔ H.Adj 1 2 :=
    (edgeBit_eq_iff G H 1 2).mp (by omega)
  have h10 : G.Adj 1 0 ↔ H.Adj 1 0 :=
    (G.adj_comm 1 0).trans (h01.trans (H.adj_comm 0 1))
  have h20 : G.Adj 2 0 ↔ H.Adj 2 0 :=
    (G.adj_comm 2 0).trans (h02.trans (H.adj_comm 0 2))
  have h21 : G.Adj 2 1 ↔ H.Adj 2 1 :=
    (G.adj_comm 2 1).trans (h12.trans (H.adj_comm 1 2))
  ext u v
  fin_cases u <;> fin_cases v <;> simp_all

theorem internalEdgeCount_le_three (G : SimpleGraph (Fin 3)) :
    internalEdgeCount G ≤ 3 := by
  have h01 := edgeBit_le_one G 0 1
  have h02 := edgeBit_le_one G 0 2
  have h12 := edgeBit_le_one G 1 2
  unfold internalEdgeCount
  omega

theorem sum_degrees (G : SimpleGraph (Fin 3)) :
    ∑ v, graphDegree G v = 2 * internalEdgeCount G := by
  rw [Fin.sum_univ_three, degree_zero, degree_one, degree_two]
  unfold internalEdgeCount
  omega

theorem degree_le_internalEdgeCount (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v ≤ internalEdgeCount G := by
  fin_cases v
  · change graphDegree G 0 ≤ _
    rw [degree_zero]
    unfold internalEdgeCount
    omega
  · change graphDegree G 1 ≤ _
    rw [degree_one]
    unfold internalEdgeCount
    omega
  · change graphDegree G 2 ≤ _
    rw [degree_two]
    unfold internalEdgeCount
    omega

theorem degree_le_two (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v ≤ 2 := by
  have h01 := edgeBit_le_one G 0 1
  have h02 := edgeBit_le_one G 0 2
  have h12 := edgeBit_le_one G 1 2
  fin_cases v
  · change graphDegree G 0 ≤ 2
    rw [degree_zero]
    omega
  · change graphDegree G 1 ≤ 2
    rw [degree_one]
    omega
  · change graphDegree G 2 ≤ 2
    rw [degree_two]
    omega

theorem one_le_degree_of_two_edges (G : SimpleGraph (Fin 3))
    (he : internalEdgeCount G = 2) (v : Fin 3) :
    1 ≤ graphDegree G v := by
  have h01 := edgeBit_le_one G 0 1
  have h02 := edgeBit_le_one G 0 2
  have h12 := edgeBit_le_one G 1 2
  unfold internalEdgeCount at he
  fin_cases v
  · change 1 ≤ graphDegree G 0
    rw [degree_zero]
    omega
  · change 1 ≤ graphDegree G 1
    rw [degree_one]
    omega
  · change 1 ≤ graphDegree G 2
    rw [degree_two]
    omega

theorem degree_eq_zero_of_no_edges (G : SimpleGraph (Fin 3))
    (he : internalEdgeCount G = 0) (v : Fin 3) : graphDegree G v = 0 := by
  have h := degree_le_internalEdgeCount G v
  omega

theorem degree_eq_two_of_three_edges (G : SimpleGraph (Fin 3))
    (he : internalEdgeCount G = 3) (v : Fin 3) : graphDegree G v = 2 := by
  have h01 := edgeBit_le_one G 0 1
  have h02 := edgeBit_le_one G 0 2
  have h12 := edgeBit_le_one G 1 2
  unfold internalEdgeCount at he
  fin_cases v
  · change graphDegree G 0 = 2
    rw [degree_zero]
    omega
  · change graphDegree G 1 = 2
    rw [degree_one]
    omega
  · change graphDegree G 2 = 2
    rw [degree_two]
    omega

def extraColumn (G : SimpleGraph (Fin 3)) (v : Fin 3) : ℕ :=
  if internalEdgeCount G = 1 then graphDegree G v
  else if internalEdgeCount G = 2 then graphDegree G v - 1 else 0

theorem extraColumn_le_one (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    extraColumn G v ≤ 1 := by
  unfold extraColumn
  split
  · have h := degree_le_internalEdgeCount G v
    omega
  · split
    · have h := degree_le_two G v
      omega
    · omega

theorem sum_extraColumn (G : SimpleGraph (Fin 3)) :
    ∑ v, extraColumn G v =
      if internalEdgeCount G = 1 then 2 else if internalEdgeCount G = 2 then 1 else 0 := by
  by_cases h1 : internalEdgeCount G = 1
  · simp only [extraColumn, h1, ite_true]
    rw [sum_degrees, h1]
  · by_cases h2 : internalEdgeCount G = 2
    · simp only [extraColumn, h2, show (2 : ℕ) ≠ 1 by decide, ite_false, ite_true, Fin.sum_univ_three]
      have hsum := sum_degrees G
      rw [Fin.sum_univ_three, h2] at hsum
      have h0 := one_le_degree_of_two_edges G h2 0
      have h1 := one_le_degree_of_two_edges G h2 1
      have h2 := one_le_degree_of_two_edges G h2 2
      omega
    · simp [extraColumn, h1, h2]

theorem degree_from_extraColumn (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v =
      if internalEdgeCount G = 0 then 0
      else if internalEdgeCount G = 1 then extraColumn G v
      else if internalEdgeCount G = 2 then extraColumn G v + 1 else 2 := by
  have he := internalEdgeCount_le_three G
  have hcases : internalEdgeCount G = 0 ∨ internalEdgeCount G = 1 ∨
      internalEdgeCount G = 2 ∨ internalEdgeCount G = 3 := by omega
  rcases hcases with h | h | h | h
  · simp [h, degree_eq_zero_of_no_edges G h v]
  · simp [h, extraColumn]
  · have hd := one_le_degree_of_two_edges G h v
    simp [h, extraColumn]
    omega
  · simp [h, degree_eq_two_of_three_edges G h v]

theorem encoded_graph_injective : Function.Injective
    (fun G : SimpleGraph (Fin 3) => (internalEdgeCount G, extraColumn G)) := by
  intro G H h
  have he : internalEdgeCount G = internalEdgeCount H := congrArg Prod.fst h
  have hx : extraColumn G = extraColumn H := congrArg Prod.snd h
  apply degree_injective
  funext v
  change graphDegree G v = graphDegree H v
  rw [degree_from_extraColumn, degree_from_extraColumn, he, hx]

def oneEdgeGraph (x : Fin 3 → ℕ) : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun u v => x u = 1 ∧ x v = 1)

def twoEdgeGraph (x : Fin 3 → ℕ) : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun u v => x u = 1 ∨ x v = 1)

theorem oneEdgeGraph_spec (x : Fin 3 → ℕ) (hx : ∀ v, x v ≤ 1)
    (hs : ∑ v, x v = 2) :
    internalEdgeCount (oneEdgeGraph x) = 1 ∧ graphDegree (oneEdgeGraph x) = x := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  rw [Fin.sum_univ_three] at hs
  have hcases : (x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 1) ∨
      (x 0 = 1 ∧ x 1 = 0 ∧ x 2 = 1) ∨
      (x 0 = 1 ∧ x 1 = 1 ∧ x 2 = 0) := by omega
  rcases hcases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  all_goals
    have hd0 : graphDegree (oneEdgeGraph x) 0 = x 0 := by
      rw [degree_zero]
      simp [edgeBit, oneEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    have hd1 : graphDegree (oneEdgeGraph x) 1 = x 1 := by
      rw [degree_one]
      simp [edgeBit, oneEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    have hd2 : graphDegree (oneEdgeGraph x) 2 = x 2 := by
      rw [degree_two]
      simp [edgeBit, oneEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    refine ⟨?_, ?_⟩
    · simp [internalEdgeCount, edgeBit, oneEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    · funext v
      fin_cases v
      · exact hd0
      · exact hd1
      · exact hd2

theorem twoEdgeGraph_spec (x : Fin 3 → ℕ) (hx : ∀ v, x v ≤ 1)
    (hs : ∑ v, x v = 1) :
    internalEdgeCount (twoEdgeGraph x) = 2 ∧
      graphDegree (twoEdgeGraph x) = fun v => x v + 1 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  rw [Fin.sum_univ_three] at hs
  have hcases : (x 0 = 1 ∧ x 1 = 0 ∧ x 2 = 0) ∨
      (x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 0) ∨
      (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 1) := by omega
  rcases hcases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  all_goals
    have hd0 : graphDegree (twoEdgeGraph x) 0 = x 0 + 1 := by
      rw [degree_zero]
      simp [edgeBit, twoEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    have hd1 : graphDegree (twoEdgeGraph x) 1 = x 1 + 1 := by
      rw [degree_one]
      simp [edgeBit, twoEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    have hd2 : graphDegree (twoEdgeGraph x) 2 = x 2 + 1 := by
      rw [degree_two]
      simp [edgeBit, twoEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    refine ⟨?_, ?_⟩
    · simp [internalEdgeCount, edgeBit, twoEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    · funext v
      fin_cases v
      · exact hd0
      · exact hd1
      · exact hd2

def columnSum (e : ℕ) : ℕ := if e = 1 then 2 else if e = 2 then 1 else 0

theorem exists_graph_of_column (e : ℕ) (he : e ≤ 3) (x : Fin 3 → ℕ)
    (hx : ∀ v, x v ≤ 1) (hs : ∑ v, x v = columnSum e) :
    ∃ G : SimpleGraph (Fin 3), internalEdgeCount G = e ∧ extraColumn G = x := by
  have hcases : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have hx0 : ∀ v, x v = 0 := by
      have hs0 : ∑ v, x v = 0 := by simpa [columnSum] using hs
      intro v
      exact Finset.sum_eq_zero_iff.mp hs0 v (Finset.mem_univ v)
    refine ⟨⊥, ?_, ?_⟩
    · simp [internalEdgeCount, edgeBit]
    · funext v
      simp [extraColumn, internalEdgeCount, edgeBit, hx0]
  · have hs2 : ∑ v, x v = 2 := by simpa [columnSum] using hs
    obtain ⟨he, hd⟩ := oneEdgeGraph_spec x hx hs2
    refine ⟨oneEdgeGraph x, he, ?_⟩
    funext v
    simp only [extraColumn, he, ite_true, hd]
  · have hs1 : ∑ v, x v = 1 := by simpa [columnSum] using hs
    obtain ⟨he, hd⟩ := twoEdgeGraph_spec x hx hs1
    refine ⟨twoEdgeGraph x, he, ?_⟩
    funext v
    simp [extraColumn, he, hd]
  · have hx0 : ∀ v, x v = 0 := by
      have hs0 : ∑ v, x v = 0 := by simpa [columnSum] using hs
      intro v
      exact Finset.sum_eq_zero_iff.mp hs0 v (Finset.mem_univ v)
    refine ⟨⊤, ?_, ?_⟩
    · simp [internalEdgeCount, edgeBit]
    · funext v
      simp [extraColumn, internalEdgeCount, edgeBit, hx0]

abbrev Column (e : ℕ) :=
  {x : Fin 3 → ℕ // (∀ v, x v ≤ 1) ∧ ∑ v, x v = columnSum e}

def fixedEdgeEncodingEquiv (e : ℕ) (he : e ≤ 3) :
    {G : SimpleGraph (Fin 3) // internalEdgeCount G = e} ≃ Column e := by
  let F : {G : SimpleGraph (Fin 3) // internalEdgeCount G = e} → Column e :=
    fun G => ⟨extraColumn G.val, extraColumn_le_one G.val, by
      simpa only [columnSum, G.property] using sum_extraColumn G.val⟩
  apply Equiv.ofBijective F
  constructor
  · intro G H h
    apply Subtype.ext
    apply encoded_graph_injective
    apply Prod.ext
    · exact G.property.trans H.property.symm
    · exact congrArg Subtype.val h
  · intro x
    obtain ⟨G, hG, hx⟩ := exists_graph_of_column e he x.val x.property.1 x.property.2
    refine ⟨⟨G, hG⟩, ?_⟩
    apply Subtype.ext
    exact hx

end Problem315.TripleInternalEncoding

end

end OAI
