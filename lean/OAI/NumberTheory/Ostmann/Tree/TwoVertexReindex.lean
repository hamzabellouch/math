import Mathlib.Data.Fintype.Sum
import OAI.NumberTheory.Ostmann.Construction.MatchedGraphQuotient

namespace OAI

/-! # Isolating two selected actual vertices without changing a graph product -/

namespace Ostmann

open scoped Classical

abbrev OtherVertices {V : Type*} (a b : V) := {v : V // v ≠ a ∧ v ≠ b}

noncomputable def twoVertexEquiv {V : Type*} (a b : V) (hab : a ≠ b) :
    (Bool ⊕ OtherVertices a b) ≃ V where
  toFun v := match v with
    | .inl true => a
    | .inl false => b
    | .inr v => v.val
  invFun v := if ha : v = a then .inl true else
    if hb : v = b then .inl false else .inr ⟨v, ha, hb⟩
  left_inv v := by
    cases v with
    | inl t => cases t <;> simp [hab.symm]
    | inr v => simp [v.property.1, v.property.2]
  right_inv v := by
    dsimp only
    split_ifs with ha hb
    · exact ha.symm
    · exact hb.symm
    · rfl

@[simp] theorem twoVertexEquiv_short {V : Type*} (a b : V) (hab : a ≠ b) :
    twoVertexEquiv a b hab (.inl true) = a := rfl

@[simp] theorem twoVertexEquiv_long {V : Type*} (a b : V) (hab : a ≠ b) :
    twoVertexEquiv a b hab (.inl false) = b := rfl

@[simp] theorem twoVertexEquiv_other {V : Type*} (a b : V) (hab : a ≠ b)
    (v : OtherVertices a b) : twoVertexEquiv a b hab (.inr v) = v := rfl

/-- Reindexing is exact even when the unary factors contain role membership
or counterpart-prior restrictions. -/
theorem finiteEdgeWeight_two_vertices {V : Type*} [Fintype V] (a b : V) (hab : a ≠ b)
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) (graph : V → V → ℤ)
    (ν : V → ℕ → ℂ) (p : Bool ⊕ OtherVertices a b → ℕ) :
    finiteEdgeWeight (dirichletGraphEdge (fun i => χ (twoVertexEquiv a b hab i))
        (fun i j => graph (twoVertexEquiv a b hab i) (twoVertexEquiv a b hab j)))
      (fun i => ν (twoVertexEquiv a b hab i)) p =
    finiteEdgeWeight (dirichletGraphEdge χ graph) ν (fun v => p ((twoVertexEquiv a b hab).symm v)) := by
  classical
  have h := finiteEdgeWeight_equiv (twoVertexEquiv a b hab)
    (dirichletGraphEdge χ graph) ν (fun v => p ((twoVertexEquiv a b hab).symm v))
  have hp : (fun i => p ((twoVertexEquiv a b hab).symm (twoVertexEquiv a b hab i))) = p := by
    funext i
    rw [Equiv.symm_apply_apply]
  change finiteEdgeWeight
    (fun i j => dirichletGraphEdge χ graph (twoVertexEquiv a b hab i) (twoVertexEquiv a b hab j))
    (fun i => ν (twoVertexEquiv a b hab i))
    (fun i => p ((twoVertexEquiv a b hab).symm (twoVertexEquiv a b hab i))) = _ at h
  rw [hp] at h
  exact h

theorem reindexed_one_sided_conditions {V : Type*} (a b : V) (hab : a ≠ b)
    (graph : V → V → ℤ) (hself : graph a a = 0 ∧ graph b b = 0)
    (hreverse : graph b a = 0) :
    let e := twoVertexEquiv a b hab
    (graph (e (.inl true)) (e (.inl true)) = 0 ∧
      graph (e (.inl false)) (e (.inl false)) = 0) ∧
      graph (e (.inl false)) (e (.inl true)) = 0 := ⟨hself, hreverse⟩

/-- All the unselected vertices are fixed only after the two genuine labels
have been isolated. Their factors contribute bounded unary functions. -/
theorem selected_graph_factorization {V : Type*} [Fintype V] (a b : V) (hab : a ≠ b)
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) (graph : V → V → ℤ)
    (ν : V → ℕ → ℂ) (outside : OtherVertices a b → ℕ)
    (hν : ∀ v x, ‖ν v x‖ ≤ 1) (hself : graph a a = 0 ∧ graph b b = 0)
    (hreverse : graph b a = 0) (hforward : graph a b ≠ 0) :
    ∃ U W : ℕ → ℂ, (∀ p, ‖U p‖ ≤ 1) ∧ (∀ q, ‖W q‖ ≤ 1) ∧
      ∀ q p, finiteEdgeWeight (dirichletGraphEdge χ graph) ν
        (fun v => twoVertexLabels outside q p ((twoVertexEquiv a b hab).symm v)) =
          U p * W q * (χ a q ^ graph a b) (p : ZMod q) := by
  let e := twoVertexEquiv a b hab
  obtain ⟨U, W, hU, hW, hfactor⟩ := dirichlet_one_sided_graph_factorization
    (fun v => χ (e v)) (fun v w => graph (e v) (e w)) (fun v => ν (e v)) outside
    (fun v x => hν (e v) x) hself hreverse hforward
  refine ⟨U, W, hU, hW, ?_⟩
  intro q p
  rw [← finiteEdgeWeight_two_vertices a b hab χ graph ν (twoVertexLabels outside q p)]
  exact hfactor q p

end Ostmann

end OAI
