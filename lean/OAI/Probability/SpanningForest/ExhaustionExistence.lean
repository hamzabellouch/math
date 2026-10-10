import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

namespace Problem336

theorem reflTransGen_finite_rooted_support {α : Type*} [DecidableEq α]
    {r : α → α → Prop} {a b : α} (h : Relation.ReflTransGen r a b) :
    ∃ S : Finset α, a ∈ S ∧ b ∈ S ∧
      ∀ v ∈ S, Relation.ReflTransGen
        (fun x y => x ∈ S ∧ y ∈ S ∧ r x y) a v := by
  induction h with
  | refl =>
      refine ⟨{a}, by simp, by simp, ?_⟩
      intro v hv
      have : v = a := Finset.mem_singleton.mp hv
      subst v
      exact .refl
  | @tail b c hab hbc ih =>
      obtain ⟨S, ha, hb, hS⟩ := ih
      have lift {v : α} (hv : v ∈ S) :
          Relation.ReflTransGen
            (fun x y => x ∈ insert c S ∧ y ∈ insert c S ∧ r x y) a v :=
        Relation.ReflTransGen.mono (fun x y hxy =>
          ⟨Finset.mem_insert_of_mem hxy.1,
            Finset.mem_insert_of_mem hxy.2.1, hxy.2.2⟩) a v (hS v hv)
      refine ⟨insert c S, Finset.mem_insert_of_mem ha, by simp, ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact (lift hb).tail
          ⟨Finset.mem_insert_of_mem hb, Finset.mem_insert_self _ _, hbc⟩
      · exact lift hv

def inducedFiniteCode (G : GraphCode) (S : Finset ℕ) : FiniteSubgraphCode := by
  classical
  exact (S, (S.product S).filter (fun p => p.1 < p.2 ∧ Adj G p.1 p.2))

@[simp] theorem mem_inducedFiniteCode_edges {G : GraphCode} {S : Finset ℕ}
    {u v : ℕ} :
    (u, v) ∈ (inducedFiniteCode G S).2 ↔
      u ∈ S ∧ v ∈ S ∧ u < v ∧ Adj G u v := by
  classical
  constructor
  · intro h
    have hfilter := Finset.mem_filter.mp h
    have hprod := Finset.mem_product.mp hfilter.1
    exact ⟨hprod.1, hprod.2, hfilter.2.1, hfilter.2.2⟩
  · rintro ⟨hu, hv, hlt, hadj⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hlt, hadj⟩

private theorem adj_symm_exhaustion {G : GraphCode} {u v : ℕ}
    (h : Adj G u v) : Adj G v u := by
  unfold Adj at *
  rw [G.2.2 v u]
  exact h

private theorem adj_ne_exhaustion {G : GraphCode} {u v : ℕ}
    (h : Adj G u v) : u ≠ v := by
  intro huv
  subst v
  unfold Adj at h
  rw [G.2.1 u] at h
  cases h

theorem subgraphAdj_inducedFiniteCode_iff {G : GraphCode} {S : Finset ℕ}
    {u v : ℕ} :
    SubgraphAdj (inducedFiniteCode G S) u v ↔
      u ∈ S ∧ v ∈ S ∧ Adj G u v := by
  unfold SubgraphAdj rawPair
  change (u ∈ S ∧ v ∈ S ∧
    (if u < v then (u, v) else (v, u)) ∈ (inducedFiniteCode G S).2) ↔ _
  by_cases huv : u < v
  · simp only [ite_eq_left huv, mem_inducedFiniteCode_edges]
    tauto
  · simp only [ite_eq_right huv, mem_inducedFiniteCode_edges]
    constructor
    · rintro ⟨hu, hv, _, _, _, hadj⟩
      exact ⟨hu, hv, adj_symm_exhaustion hadj⟩
    · rintro ⟨hu, hv, hadj⟩
      exact ⟨hu, hv, hv, hu,
        lt_of_le_of_ne (Nat.le_of_not_gt huv) (Ne.symm (adj_ne_exhaustion hadj)),
        adj_symm_exhaustion hadj⟩

theorem inducedFiniteCode_connected_of_rooted {G : GraphCode} {S : Finset ℕ}
    {a : ℕ} (ha : a ∈ S)
    (hS : ∀ v ∈ S, Relation.ReflTransGen
      (fun x y => x ∈ S ∧ y ∈ S ∧ Adj G x y) a v) :
    IsFiniteConnectedSubgraph G (inducedFiniteCode G S) := by
  refine ⟨⟨a, ha⟩, ?_, ?_⟩
  · intro p hp
    exact mem_inducedFiniteCode_edges.mp hp
  · intro u hu v hv
    have forward (w : ℕ) (hw : w ∈ S) :
        Relation.ReflTransGen (SubgraphAdj (inducedFiniteCode G S)) a w :=
      Relation.ReflTransGen.mono
        (fun x y hxy => subgraphAdj_inducedFiniteCode_iff.mpr hxy) a w (hS w hw)
    have backward : Relation.ReflTransGen (SubgraphAdj (inducedFiniteCode G S)) u a := by
      have h := forward u hu
      induction h with
      | refl => exact .refl
      | @tail b c hab hbc ih =>
          have hc := subgraphAdj_inducedFiniteCode_iff.mp hbc
          exact (Relation.ReflTransGen.single
            (subgraphAdj_inducedFiniteCode_iff.mpr
              ⟨hc.2.1, hc.1, adj_symm_exhaustion hc.2.2⟩)).trans (ih hc.1)
    exact backward.trans (forward v hv)

theorem GraphConnected.exists_connected_exhaustion {G : GraphCode}
    (hG : GraphConnected G) :
    ∃ H : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H := by
  classical
  have supports : ∀ n : ℕ, ∃ S : Finset ℕ, 0 ∈ S ∧ n ∈ S ∧
      ∀ v ∈ S, Relation.ReflTransGen
        (fun x y => x ∈ S ∧ y ∈ S ∧ Adj G x y) 0 v :=
    fun n => reflTransGen_finite_rooted_support (hG 0 n)
  choose S hzero hn hroot using supports
  let V : ℕ → Finset ℕ := fun n => (Finset.range (n + 1)).biUnion S
  have hsub {n i : ℕ} (hi : i ≤ n) : S i ⊆ V n := by
    intro u hu
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), hu⟩
  have hvertex (n : ℕ) : n ∈ V n := hsub (le_refl n) (hn n)
  have hzeroV (n : ℕ) : 0 ∈ V n := hsub (Nat.zero_le n) (hzero 0)
  have hmono {n m : ℕ} (hnm : n ≤ m) : V n ⊆ V m := by
    intro u hu
    obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hu
    exact hsub (by have := Finset.mem_range.mp hi; omega) hui
  have hrootV (n : ℕ) (v : ℕ) (hv : v ∈ V n) :
      Relation.ReflTransGen
        (fun x y => x ∈ V n ∧ y ∈ V n ∧ Adj G x y) 0 v := by
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
    have hisub : S i ⊆ V n := hsub (by have := Finset.mem_range.mp hi; omega)
    exact Relation.ReflTransGen.mono
      (fun x y hxy => ⟨hisub hxy.1, hisub hxy.2.1, hxy.2.2⟩)
      0 v (hroot i v hvi)
  refine ⟨fun n => inducedFiniteCode G (V n), ?_, ?_, ?_⟩
  · intro n
    exact inducedFiniteCode_connected_of_rooted (hzeroV n) (hrootV n)
  · intro n
    refine ⟨hmono (Nat.le_succ n), ?_⟩
    intro p hp
    obtain ⟨hu, hv, hlt, hadj⟩ := mem_inducedFiniteCode_edges.mp hp
    exact mem_inducedFiniteCode_edges.mpr
      ⟨hmono (Nat.le_succ n) hu, hmono (Nat.le_succ n) hv, hlt, hadj⟩
  · intro u v huv hadj
    refine ⟨v, mem_inducedFiniteCode_edges.mpr ?_⟩
    exact ⟨hmono (Nat.le_of_lt huv) (hvertex u), hvertex v, huv, hadj⟩

theorem GraphConnected.exists_finite_induced_containing {G : GraphCode}
    (hG : GraphConnected G) (V : Finset ℕ) :
    ∃ S : Finset ℕ, V ⊆ S ∧
      IsFiniteConnectedSubgraph G (inducedFiniteCode G S) := by
  classical
  have supports : ∀ n : ℕ, ∃ S : Finset ℕ, 0 ∈ S ∧ n ∈ S ∧
      ∀ v ∈ S, Relation.ReflTransGen
        (fun x y => x ∈ S ∧ y ∈ S ∧ Adj G x y) 0 v :=
    fun n => reflTransGen_finite_rooted_support (hG 0 n)
  choose S hzero hn hroot using supports
  let W : Finset ℕ := (insert 0 V).biUnion S
  have hsub {i : ℕ} (hi : i ∈ insert 0 V) : S i ⊆ W := by
    intro u hu
    exact Finset.mem_biUnion.mpr ⟨i, hi, hu⟩
  refine ⟨W, ?_, inducedFiniteCode_connected_of_rooted
    (hsub (Finset.mem_insert_self 0 V) (hzero 0)) ?_⟩
  · intro u hu
    exact hsub (Finset.mem_insert_of_mem hu) (hn u)
  · intro v hv
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
    exact Relation.ReflTransGen.mono
      (fun x y hxy => ⟨hsub hi hxy.1, hsub hi hxy.2.1, hxy.2.2⟩)
      0 v (hroot i v hvi)

theorem GraphConnected.exists_finiteConnected_containing {G : GraphCode}
    (hG : GraphConnected G) (V : Finset ℕ) :
    ∃ K : FiniteSubgraphCode, IsFiniteConnectedSubgraph G K ∧ V ⊆ K.1 := by
  obtain ⟨S, hVS, hS⟩ := hG.exists_finite_induced_containing V
  exact ⟨inducedFiniteCode G S, hS, hVS⟩

theorem GraphConnected.exists_finiteConnected_extension {G : GraphCode}
    (hG : GraphConnected G) (K₀ : FiniteSubgraphCode)
    (hE : ∀ p ∈ K₀.2, p.1 < p.2 ∧ Adj G p.1 p.2) :
    ∃ K : FiniteSubgraphCode, IsFiniteConnectedSubgraph G K ∧
      K₀.1 ⊆ K.1 ∧ K₀.2 ⊆ K.2 := by
  classical
  let V := K₀.1 ∪ K₀.2.image Prod.fst ∪ K₀.2.image Prod.snd
  obtain ⟨S, hVS, hS⟩ := hG.exists_finite_induced_containing V
  refine ⟨inducedFiniteCode G S, hS, ?_, ?_⟩
  · intro u hu
    exact hVS (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  · intro p hp
    apply mem_inducedFiniteCode_edges.mpr
    refine ⟨hVS ?_, hVS ?_, (hE p hp).1, (hE p hp).2⟩
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.fst hp))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd hp)

end Problem336

end

end OAI
