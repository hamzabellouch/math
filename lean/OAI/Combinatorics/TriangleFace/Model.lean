import OAI.Combinatorics.MatchingEntropy.TriangleExpansion

namespace OAI

namespace CanonicalFace198

variable {A B : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup B] [Module ℝ B]

def facesThrough (P : Set A) (x : A) : Set (Set A) :=
  {F | Convex ℝ F ∧ IsExtreme ℝ P F ∧ x ∈ F}

def minFace (P : Set A) (x : A) : Set A := ⋂₀ facesThrough P x

end CanonicalFace198

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def LocalLabels (G : LooplessGraph V E) (v : V) (c : E → Fin 3) : Prop :=
  ∀ i, ∃! e, G.Incident v e ∧ c e = i

def localEdge (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) (i : Fin 3) : E := Classical.choose (hc i)

def localExtension (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) : (E → ℝ) →ₗ[ℝ] (E ⊕ Fin 3 → ℝ) where
  toFun x := Sum.elim x (fun i => x (localEdge G c v hc i))
  map_add' x y := by ext e; cases e <;> rfl
  map_smul' a x := by ext e; cases e <;> rfl

def oldRestriction : (E ⊕ Fin 3 → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun y e := y (Sum.inl e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end TriangleFace198

end

end OAI
