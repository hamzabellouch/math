import OAI.Probability.SpanningForest.WeightedTreeTransport
import OAI.Probability.SpanningForest.FiniteUSTRelabel

namespace OAI

noncomputable section

namespace Problem336.WeightedTree

private theorem tree_canonical {K : FiniteSubgraphCode}
    (hK : ∀ p ∈ K.2, p.1 < p.2) (T : USTResponse.TreeSample K) :
    ∀ p ∈ T.1, p.1 < p.2 :=
  fun p hp => hK p ((USTResponse.tree_property K T).1 hp)

def treeRelabelEquiv (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) :
    USTResponse.TreeSample K ≃ USTResponse.TreeSample (relabelFiniteSubgraph σ K) where
  toFun T := ⟨relabelEdgeSet σ T.1, by
    rw [spanningTrees_relabel σ K hK]
    exact Finset.mem_image.mpr ⟨T.1, T.2, rfl⟩⟩
  invFun T := ⟨relabelEdgeSet σ.symm T.1, by
    have hm : T.1 ∈ (spanningTrees K).image (relabelEdgeSet σ) := by
      simpa only [spanningTrees_relabel σ K hK] using T.2
    obtain ⟨S, hS, heq⟩ := Finset.mem_image.mp hm
    rw [← heq, relabelEdgeSet_symm σ S (tree_canonical hK ⟨S, hS⟩)]
    exact hS⟩
  left_inv T := Subtype.ext (relabelEdgeSet_symm σ T.1 (tree_canonical hK T))
  right_inv T := by
    apply Subtype.ext
    exact relabelEdgeSet_symm σ.symm T.1
      (tree_canonical (relabelEdgeSet_valid σ K.2 hK) T)

@[simp] theorem treeRelabelEquiv_val (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) (T : USTResponse.TreeSample K) :
    (treeRelabelEquiv σ K hK T).1 = relabelEdgeSet σ T.1 := rfl

def relabelField (σ : Equiv ℕ ℕ) (h : Field) : Field :=
  fun p => h (relabelPair σ.symm p)

@[simp] theorem relabelField_mapEdge (σ : Equiv ℕ ℕ) (h : Field) (e : EdgeCode) :
    relabelField σ h (mapEdge σ e).1 = h e.1 := by
  unfold relabelField
  rw [← relabelPair_edge, relabelPair_symm σ e.2]

theorem inclusion_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) (h : Field) (e : EdgeCode) :
    inclusion (relabelFiniteSubgraph σ K) (mapEdge σ e).1 (relabelField σ h) =
      inclusion K e.1 h := by
  apply inclusion_eq_of_tree_equiv K _ (treeRelabelEquiv σ K hK) h
    (relabelField σ h) e.1 (mapEdge σ e).1
  · intro T
    apply weight_image
    · intro p hp q hq hpq
      exact relabelPair_injOn σ (tree_canonical hK T p hp)
        (tree_canonical hK T q hq) hpq
    · intro p hp
      simpa only [← relabelPair_edge] using
        relabelField_mapEdge σ h ⟨p, tree_canonical hK T p hp⟩
  · intro T
    exact mem_relabelEdgeSet_iff σ T.1 (tree_canonical hK T) e

theorem finiteField_relabel_mapEdge (σ : Equiv ℕ ℕ) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, p.1 < p.2) (t : ℝ) (h : Field) (e : EdgeCode) :
    finiteField (relabelEdgeSet σ S) t (relabelField σ h) (mapEdge σ e).1 =
      finiteField S t h e.1 := by
  simp only [finiteField, mem_relabelEdgeSet_iff σ S hS e, relabelField_mapEdge]

theorem finiteTilt_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, p.1 < p.2) (t : ℝ) (h : Field) (e : EdgeCode) :
    inclusion (relabelFiniteSubgraph σ K) (mapEdge σ e).1
        (finiteField (relabelEdgeSet σ S) t (relabelField σ h)) =
      inclusion K e.1 (finiteField S t h) := by
  apply inclusion_eq_of_tree_equiv K _ (treeRelabelEquiv σ K hK)
    (finiteField S t h) _ e.1 (mapEdge σ e).1
  · intro T
    apply weight_image
    · intro p hp q hq hpq
      exact relabelPair_injOn σ (tree_canonical hK T p hp)
        (tree_canonical hK T q hq) hpq
    · intro p hp
      simpa only [← relabelPair_edge] using
        finiteField_relabel_mapEdge σ S hS t h ⟨p, tree_canonical hK T p hp⟩
  · intro T
    exact mem_relabelEdgeSet_iff σ T.1 (tree_canonical hK T) e

theorem inclusion_congr_on_edges (K : FiniteSubgraphCode) (a b : Field)
    (e : ℕ × ℕ) (h : ∀ p ∈ K.2, a p = b p) :
    inclusion K e a = inclusion K e b := by
  symm
  apply inclusion_eq_of_tree_equiv K K (Equiv.refl _) a b e e
  · intro T
    unfold weight
    congr 1
    exact Finset.sum_congr rfl (fun p hp =>
      (h p ((USTResponse.tree_property K T).1 hp)).symm)
  · intro T
    rfl

theorem extendField_relabel_canonical (σ : Equiv ℕ ℕ) (y : EdgeCode → ℝ)
    (p : ℕ × ℕ) (hp : p.1 < p.2) :
    extendField (fun e => y (mapEdge σ.symm e)) p =
      relabelField σ (extendField y) p := by
  let e : EdgeCode := ⟨p, hp⟩
  change extendField (fun e => y (mapEdge σ.symm e)) e.1 =
    extendField y (relabelPair σ.symm e.1)
  rw [relabelPair_edge, extendField_apply, extendField_apply]

theorem finiteTilt_edgeField_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, p.1 < p.2) (t : ℝ) (y : EdgeCode → ℝ) (e : EdgeCode) :
    inclusion (relabelFiniteSubgraph σ K) (mapEdge σ e).1
        (finiteField (relabelEdgeSet σ S) t
          (extendField (fun f => y (mapEdge σ.symm f)))) =
      inclusion K e.1 (finiteField S t (extendField y)) := by
  rw [← finiteTilt_relabel σ K hK S hS t (extendField y) e]
  apply inclusion_congr_on_edges
  intro p hp
  have hp' : p.1 < p.2 := relabelEdgeSet_valid σ K.2 hK p hp
  simp only [finiteField, extendField_relabel_canonical σ y p hp']

end Problem336.WeightedTree

end

end OAI
