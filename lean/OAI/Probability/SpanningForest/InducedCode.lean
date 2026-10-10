import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section
namespace Problem336

def inducedCode (G : GraphCode) (S : Finset ℕ) : FiniteSubgraphCode := by
  classical
  exact (S, (S.product S).filter (fun p => p.1 < p.2 ∧ Adj G p.1 p.2))

@[simp] theorem inducedCode_vertices (G : GraphCode) (S : Finset ℕ) :
    (inducedCode G S).1 = S := rfl

@[simp] theorem mem_inducedCode_edges (G : GraphCode) (S : Finset ℕ) (p : ℕ × ℕ) :
    p ∈ (inducedCode G S).2 ↔ p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧ Adj G p.1 p.2 := by
  classical
  rcases p with ⟨u, v⟩
  simp only [inducedCode, Finset.mem_filter]
  have hprod : (u,v) ∈ S.product S ↔ u ∈ S ∧ v ∈ S := Finset.mem_product
  rw [hprod]
  tauto

private theorem inducedCode_adj_symm (G : GraphCode) (u v : ℕ) : Adj G u v ↔ Adj G v u := by
  unfold Adj
  rw [G.2.2 u v]

private theorem inducedCode_adj_ne {G : GraphCode} {u v : ℕ} (h : Adj G u v) : u ≠ v := by
  intro huv
  subst v
  unfold Adj at h
  rw [G.2.1 u] at h
  contradiction

@[simp] theorem rawPair_mem_inducedCode_edges (G : GraphCode) (S : Finset ℕ) (u v : ℕ) :
    rawPair u v ∈ (inducedCode G S).2 ↔ u ∈ S ∧ v ∈ S ∧ Adj G u v := by
  rw [mem_inducedCode_edges]
  by_cases h : u < v
  · simp only [rawPair, ite_eq_left h]
    tauto
  · simp only [rawPair, ite_eq_right h]
    constructor
    · rintro ⟨hv, hu, _, hadj⟩
      exact ⟨hu, hv, (inducedCode_adj_symm G v u).mp hadj⟩
    · rintro ⟨hu, hv, hadj⟩
      exact ⟨hv, hu, by have := inducedCode_adj_ne hadj; omega,
        (inducedCode_adj_symm G u v).mp hadj⟩

@[simp] theorem subgraphAdj_inducedCode (G : GraphCode) (S : Finset ℕ) (u v : ℕ) :
    SubgraphAdj (inducedCode G S) u v ↔ u ∈ S ∧ v ∈ S ∧ Adj G u v := by
  simp only [SubgraphAdj, inducedCode_vertices, rawPair_mem_inducedCode_edges]
  tauto

theorem inducedCode_isFiniteConnectedSubgraph {G : GraphCode} {S : Finset ℕ}
    (hS : S.Nonempty)
    (hconn : ∀ u ∈ S, ∀ v ∈ S,
      Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj G a b) u v) :
    IsFiniteConnectedSubgraph G (inducedCode G S) := by
  refine ⟨hS, ?_, ?_⟩
  · intro p hp
    exact (mem_inducedCode_edges G S p).mp hp
  · intro u hu v hv
    exact Relation.ReflTransGen.mono
      (fun a b h => (subgraphAdj_inducedCode G S a b).mpr h) _ _ (hconn u hu v hv)

theorem inducedCode_mono (G : GraphCode) {S T : Finset ℕ} (h : S ⊆ T) :
    (inducedCode G S).1 ⊆ (inducedCode G T).1 ∧
      (inducedCode G S).2 ⊆ (inducedCode G T).2 := by
  refine ⟨h, ?_⟩
  intro p hp
  rcases (mem_inducedCode_edges G S p).mp hp with ⟨hu, hv, hlt, hadj⟩
  exact (mem_inducedCode_edges G T p).mpr ⟨h hu, h hv, hlt, hadj⟩

theorem inducedCode_isConnectedExhaustion {G : GraphCode} (S : ℕ → Finset ℕ)
    (hne : ∀ n, (S n).Nonempty)
    (hconn : ∀ n, ∀ u ∈ S n, ∀ v ∈ S n,
      Relation.ReflTransGen (fun a b => a ∈ S n ∧ b ∈ S n ∧ Adj G a b) u v)
    (hmono : Monotone S)
    (hcover : ∀ v, ∃ n, v ∈ S n) :
    IsConnectedExhaustion G (fun n => inducedCode G (S n)) := by
  refine ⟨fun n => inducedCode_isFiniteConnectedSubgraph (hne n) (hconn n),
    fun n => inducedCode_mono G (hmono (Nat.le_succ n)), ?_⟩
  intro u v huv hadj
  obtain ⟨nu, hnu⟩ := hcover u
  obtain ⟨nv, hnv⟩ := hcover v
  refine ⟨max nu nv, (mem_inducedCode_edges G (S (max nu nv)) (u, v)).mpr ?_⟩
  exact ⟨hmono (le_max_left nu nv) hnu, hmono (le_max_right nu nv) hnv, huv, hadj⟩

theorem measurable_inducedCode {X : Type*} [MeasurableSpace X]
    {G : X → GraphCode} {S : X → Finset ℕ}
    (hG : Measurable G) (hS : Measurable S) :
    Measurable (fun x => inducedCode (G x) (S x)) := by
  have hedges : Measurable (fun x => (inducedCode (G x) (S x)).2) := by
    apply measurable_finset_iff.mpr
    intro p
    have ha : Measurable (fun x => Adj (G x) p.1 p.2) := by
      exact ((measurable_pi_apply p.2).comp
        ((measurable_pi_apply p.1).comp (measurable_subtype_coe.comp hG))).eq_const true
    have hu := (measurable_finset_iff.mp hS) p.1
    have hv := (measurable_finset_iff.mp hS) p.2
    simpa only [mem_inducedCode_edges] using hu.and (hv.and (measurable_const.and ha))
  exact hS.prodMk hedges

end Problem336

end

end OAI
