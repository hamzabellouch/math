import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.OrientedPivotTree
import OAI.Combinatorics.RamseyFive.Trees.TreeOriginalTrims
import OAI.Combinatorics.RamseyFive.Entropy.Swap
import OAI.Combinatorics.RamseyFive.Trees.TreeDecoder

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type}

noncomputable def orientedPivotContextAt
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (b : BinaryTree I) (ω : OrientedPivotTreeTape f r b)
    (C : PivotContext K V) (j : Address b) : Option (PivotContext K V) :=
  contextAt (fun _ : I => OrientedPivotTape f r) (fun _ : I => OrientedPivotMessage f r)
    (fun _ : I => orientedPivotLeft f r) (fun _ : I => orientedPivotRight f r)
    (fun i C t => orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t) b ω C j

theorem oriented_original_point_trim
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (X : Finset (ℙ K V)) (b : BinaryTree I) (j : Address b) :
    eventMass (orientedPivotTreeLaw f r b) (Finset.univ.filter (fun ω => ∃ C,
      orientedPivotContextAt f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c δ τ P hδ b ω
        (Finset.univ,Finset.univ) j = some C ∧
      ((X ∩ C.1).card : ℝ) < (9/10:ℝ)*X.card)) ≤
      10 * pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass (fun b a => Incident a b) (uniformWeight (B₀ i)) (uniformWeight X))
        (fun _ => 0) b j := by
  let Ω := fun _ : I => OrientedPivotTape f r
  let M := fun _ : I => OrientedPivotMessage f r
  let p := fun (_ : I) C => orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)
  let out : ∀ i C t, M i C t → Finset (ℙ K V) × Finset (ℙ K (Dual K V)) :=
    fun _ C t m => (orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t m).swap
  let enc : ∀ i C t, Option (M i C t) := fun i C t =>
    orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t
  apply first_original_trim Ω p M out enc X
  · intro i
    apply mul_nonneg (by positivity)
    exact relationMass_nonneg _ _ _ (uniformWeight_nonneg _) (uniformWeight_nonneg _)
  · intro i C
    exact oriented_point_cap_eviction (f C) (r C) σ hσ hq hd hq3
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hc hc9 hδ hτ X

theorem oriented_original_dual_trim
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (X : Finset (ℙ K (Dual K V))) (b : BinaryTree I) (j : Address b) :
    eventMass (orientedPivotTreeLaw f r b) (Finset.univ.filter (fun ω => ∃ C,
      orientedPivotContextAt f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c δ τ P hδ b ω
        (Finset.univ,Finset.univ) j = some C ∧
      ((X ∩ C.2).card : ℝ) < (9/10:ℝ)*X.card)) ≤
      10 * pathBudget (fun _ => 0)
        (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) *
          relationMass Incident (uniformWeight (A₀ i)) (uniformWeight X)) b j := by
  let Ω := fun _ : I => OrientedPivotTape f r
  let M := fun _ : I => OrientedPivotMessage f r
  let p := fun (_ : I) C => orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)
  let out : ∀ i C t, M i C t → Finset (ℙ K V) × Finset (ℙ K (Dual K V)) :=
    fun _ C t m => (orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t m).swap
  let enc : ∀ i C t, Option (M i C t) := fun i C t =>
    orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t
  apply second_original_trim Ω p M out enc X
  · intro i
    apply mul_nonneg (by positivity)
    exact relationMass_nonneg _ _ _ (uniformWeight_nonneg _) (uniformWeight_nonneg _)
  · intro i C
    exact oriented_dual_cap_eviction (f C) (r C) σ hσ hq hd hq3
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hc hc9 hδ hτ X

end SharpRamseyFive.ProjectiveIncidence

end OAI
