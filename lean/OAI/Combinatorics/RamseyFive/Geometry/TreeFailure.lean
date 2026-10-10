import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.OriginalReadiness
import OAI.Combinatorics.RamseyFive.Entropy.MeanTreeFailure

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) actualTreeFailurePropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type} [Fintype I] [DecidableEq I]
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

noncomputable def orientedPivotSuccessAt
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (b : BinaryTree I) (ω : OrientedPivotTreeTape f r b)
    (C : PivotContext K V) (j : Address b) : Option Unit :=
  successAt (fun _ : I => OrientedPivotTape f r) (fun _ : I => OrientedPivotMessage f r)
    (fun _ : I => orientedPivotLeft f r) (fun _ : I => orientedPivotRight f r)
    (fun i C t => orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t) b ω C j

theorem oriented_original_tree_missing
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a) ≤ L*p i a)
    (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b) ≤ L*q i b)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2) (hτpos : 0<τ)
    (ε : I → ℝ) (hε : ∀ i, 0≤ε i)
    (hlocal : ∀ i a b C, OriginalNodeReady (X i a) C.1 (Y i b) C.2 (9/10) τ →
      eventMass (orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K))
        (Finset.univ.filter (fun t => orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
          (X i a) C.1 (Y i b) C.2 (hX i a) (hY i b) c δ τ P hδ t = none)) ≤ ε i)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω =>
        orientedPivotSuccessAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j = none))) ≤
    pathSum tree (fun k =>
      10 * pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) * L^2 *
        relationMass Incident (p (label tree k)) (q i)) (fun _ => 0) tree k +
      10 * pathBudget (fun _ => 0) (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) * L^2 *
        relationMass Incident (p i) (q (label tree k))) tree k +
      ((Nat.card K:ℝ)/τ)*L^2*relationMass Incident (p (label tree k)) (q (label tree k)) + ε (label tree k)) j := by
  let Ω := fun _ : I => OrientedPivotTape f r
  let M := fun _ : I => OrientedPivotMessage f r
  let l := fun _ : I => orientedPivotLeft f r
  let rt := fun _ : I => orientedPivotRight f r
  let tape := fun (_ : I) C => orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)
  let enc := fun (z : (∀ i, A i) × (∀ i, B i)) i C t =>
    orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
      (X i (z.1 i)) C.1 (Y i (z.2 i)) C.2 (hX i _) (hY i _) c δ τ P hδ t
  let ready := fun (z : (∀ i, A i) × (∀ i, B i)) i (C : PivotContext K V) =>
    OriginalNodeReady (X i (z.1 i)) C.1 (Y i (z.2 i)) C.2 (9/10) τ
  apply mean_missing_mass_le Ω M l rt (originalLevelLaw μ ν) enc tree
  intro k
  have hh := mean_reached_abort Ω M l rt (originalLevelLaw μ ν) enc tape ready ε hε
    (fun z i C h => hlocal i (z.1 i) (z.2 i) C h) tree (Finset.univ,Finset.univ) k
  have hr := oriented_level_not_ready f r σ hσ hq hd hq3 μ ν X Y hX hY p q L hL hμ hν
    c δ τ P hc hc9 hδ hτ hτpos tree k
  exact hh.trans (add_le_add_left hr _)
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
