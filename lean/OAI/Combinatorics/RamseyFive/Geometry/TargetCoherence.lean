import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.TargetCaps
import OAI.Combinatorics.RamseyFive.Geometry.TreeFailure
import OAI.Combinatorics.RamseyFive.Trees.TreeObservationRelations

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma oriented_caps_none_iff
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (tree : BinaryTree I) (ω : OrientedPivotTreeTape f r tree)
    (C : PivotContext K V) (j : Address tree) :
    orientedPivotCapsAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C j = none ↔
      orientedPivotSuccessAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C j = none :=
  observe_none_iff_success (fun _ : I => OrientedPivotTape f r) (fun _ : I => OrientedPivotMessage f r)
    (fun _ : I => orientedPivotLeft f r) (fun _ : I => orientedPivotRight f r)
    (fun i C t => orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t)
    (fun _ C t => orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t)
    tree ω C j

omit [Fintype I] [DecidableEq I] in
lemma oriented_caps_context_coherent
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (tree : BinaryTree I) (ω : OrientedPivotTreeTape f r tree)
    (C : PivotContext K V) (j : Address tree) :
    orientedPivotCapsAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C j ≠ none →
      orientedPivotContextAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C j ≠ none :=
  observe_context_coherent (fun _ : I => OrientedPivotTape f r) (fun _ : I => OrientedPivotMessage f r)
    (fun _ : I => orientedPivotLeft f r) (fun _ : I => orientedPivotRight f r)
    (fun i C t => orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t)
    (fun _ C t => orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t)
    tree ω C j
end SharpRamseyFive.ProjectiveIncidence

end OAI
