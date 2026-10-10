import OAI.Combinatorics.Crossing.SurgeryCutWalks

namespace OAI

noncomputable section
namespace Zarankiewicz

def walkThroughChord {G : SimpleGraph Plane} {a u v b : Plane}
    (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b) : G.Walk a b :=
  (A.append h.toWalk).append B

theorem walkThroughChord_range {G : SimpleGraph Plane} {a u v b : Plane}
    (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b) :
    Set.range (graphWalkPath id (walkThroughChord A h B))=
      (Set.range (graphWalkPath id A) ∪ segment ℝ u v) ∪ Set.range (graphWalkPath id B) := by
  rw [walkThroughChord,graphWalkPath_append_range,graphWalkPath_append_range,graphWalkPath_toWalk_range]

theorem exists_simple_path_through_chord {G : SimpleGraph Plane}
    (hemb : StraightEdgeEmbedding G id) {a u v b : Plane} (hab : a ≠ b)
    (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b) :
    ∃ γ : Path a b, Function.Injective γ ∧ HasFiniteAffineCover γ ∧
      Set.range γ ⊆ (Set.range (graphWalkPath id A) ∪ segment ℝ u v) ∪ Set.range (graphWalkPath id B) := by
  classical
  let p := walkThroughChord A h B
  refine ⟨graphWalkPath id p.bypass,
    graphWalkPath_injective id hemb hab p.bypass p.bypass_isPath,
    graphWalkPath_hasFiniteAffineCover id p.bypass,?_⟩
  exact (graphWalkPath_bypass_range_subset id p).trans (by rw [walkThroughChord_range])

variable {m n : ℕ} {D D' : AdmissibleDrawing m n}

theorem surgery_mixed_endpoints_ne (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (p q : C.InnerIndex) : D'.vertex (.inl p.1.1) ≠ D'.vertex (.inr q.1.2) := by
  intro h
  cases D'.vertex_injective h

end Zarankiewicz

end

end OAI
