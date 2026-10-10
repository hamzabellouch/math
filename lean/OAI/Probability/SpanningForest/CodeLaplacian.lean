import OAI.Probability.SpanningForest.Definitions
import OAI.Probability.SpanningForest.ReducedLaplacian

namespace OAI

namespace Problem336

open scoped Matrix

variable {G : GraphCode} {K : FiniteSubgraphCode}

def codeSource (hK : IsFiniteConnectedSubgraph G K) (e : K.2) : K.1 :=
  ⟨e.val.1, (hK.2.1 e.val e.property).1⟩

def codeTarget (hK : IsFiniteConnectedSubgraph G K) (e : K.2) : K.1 :=
  ⟨e.val.2, (hK.2.1 e.val e.property).2.1⟩

theorem code_edgeAdj_iff (hK : IsFiniteConnectedSubgraph G K) (u v : K.1) :
    ReducedLaplacian.EdgeAdj (codeSource hK) (codeTarget hK) u v ↔
      SubgraphAdj K u.val v.val := by
  constructor
  · rintro ⟨e, h | h⟩
    · refine ⟨u.property, v.property, ?_⟩
      have hs := congrArg Subtype.val h.1
      have ht := congrArg Subtype.val h.2
      change e.val.1 = u.val at hs
      change e.val.2 = v.val at ht
      rw [← hs, ← ht]
      have hlt := (hK.2.1 e.val e.property).2.2.1
      simpa only [rawPair, ite_eq_left hlt, Prod.mk.eta] using e.property
    · refine ⟨u.property, v.property, ?_⟩
      have hs := congrArg Subtype.val h.1
      have ht := congrArg Subtype.val h.2
      change e.val.1 = v.val at hs
      change e.val.2 = u.val at ht
      rw [← hs, ← ht]
      have hlt := (hK.2.1 e.val e.property).2.2.1
      have hnot : ¬e.val.2 < e.val.1 := Nat.not_lt.mpr (Nat.le_of_lt hlt)
      simpa only [rawPair, ite_eq_right hnot, Prod.mk.eta] using e.property
  · intro h
    refine ⟨⟨rawPair u.val v.val, h.2.2⟩, ?_⟩
    by_cases huv : u.val < v.val
    · left
      constructor <;> apply Subtype.ext <;> simp [codeSource, codeTarget, rawPair, huv]
    · right
      constructor <;> apply Subtype.ext <;> simp [codeSource, codeTarget, rawPair, huv]

theorem code_endpoints_connected (hK : IsFiniteConnectedSubgraph G K) :
    ReducedLaplacian.Connected (codeSource hK) (codeTarget hK) := by
  intro u v
  have liftPath {a b : ℕ} (hab : Relation.ReflTransGen (SubgraphAdj K) a b) :
      ∀ (ha : a ∈ K.1) (hb : b ∈ K.1),
        Relation.ReflTransGen
          (ReducedLaplacian.EdgeAdj (codeSource hK) (codeTarget hK))
          (⟨a, ha⟩ : K.1) (⟨b, hb⟩ : K.1) := by
    induction hab with
    | refl => intro _ _; exact .refl
    | @tail b c hab hbc ih =>
      intro ha hc
      exact (ih ha hbc.1).tail
        ((code_edgeAdj_iff hK ⟨b, hbc.1⟩ ⟨c, hc⟩).2 hbc)
  exact liftPath (hK.2.2 u.val u.property v.val v.property) u.property v.property

def codeWeightedLaplacian (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (w : K.2 → ℝ) :
    Matrix {v : K.1 // v ≠ root} {v : K.1 // v ≠ root} ℝ :=
  ReducedLaplacian.weightedLaplacian (codeSource hK) (codeTarget hK) root w

theorem codeWeightedLaplacian_posDef (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (w : K.2 → ℝ) (hw : ∀ e, 0 < w e) :
    (codeWeightedLaplacian hK root w).PosDef :=
  ReducedLaplacian.weightedLaplacian_posDef
    (codeSource hK) (codeTarget hK) root w (code_endpoints_connected hK) hw

theorem codeWeightedLaplacian_det_ne_zero (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (w : K.2 → ℝ) (hw : ∀ e, 0 < w e) :
    (codeWeightedLaplacian hK root w).det ≠ 0 :=
  ReducedLaplacian.weightedLaplacian_det_ne_zero
    (codeSource hK) (codeTarget hK) root w (code_endpoints_connected hK) hw

end Problem336

end OAI
