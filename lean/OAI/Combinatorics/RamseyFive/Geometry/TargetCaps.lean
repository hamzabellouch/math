import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OriginalMarginalLaw

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
noncomputable section
local instance (priority := high) actualTargetCapsPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {I : Type}

noncomputable def orientedPivotCapsAt
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (b : BinaryTree I) (ω : OrientedPivotTreeTape f r b)
    (C : PivotContext K V) (j : Address b) : Option (Finset (ℙ K (Dual K V)) × Finset (ℙ K V)) :=
  observe (fun _ : I => OrientedPivotTape f r) (fun _ : I => OrientedPivotMessage f r)
    (fun _ : I => orientedPivotLeft f r) (fun _ : I => orientedPivotRight f r)
    (fun i C t => orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t)
    (fun _ C t => orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t) b ω C j

theorem oriented_original_point_cap
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (x : (ℙ K V)) (tree : BinaryTree I) (j : Address tree) :
    eventMass (orientedPivotTreeLaw f r tree) (Finset.univ.filter (fun ω =>
      Excludes x ((orientedPivotCapsAt f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω
        (Finset.univ,Finset.univ) j).map Prod.snd))) ≤
      (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass (fun b a => Incident a b) (uniformWeight (B₀ (label tree j))) (uniformWeight {x}) := by
  let Ω := fun _ : I => OrientedPivotTape f r
  let M := fun _ : I => OrientedPivotMessage f r
  let p := fun (_ : I) C => orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)
  let enc : ∀ i C t, Option (M i C t) := fun i C t =>
    orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t
  let out : ∀ i C t, M i C t → _ := fun _ C t =>
    orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t
  let rate := fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) *
    relationMass (fun b a => Incident a b) (uniformWeight (B₀ i)) (uniformWeight {x})
  have hn : ∀ i, 0≤rate i := fun i => mul_nonneg (by positivity)
    (relationMass_nonneg _ _ _ (uniformWeight_nonneg _) (uniformWeight_nonneg _))
  have hh := observe_event_bound Ω M (fun _ => orientedPivotLeft f r) (fun _ => orientedPivotRight f r)
    p enc out (fun o => Excludes x (o.map Prod.snd)) (by simp [Excludes]) rate hn
    (fun i C => by
      have h := (orientedGuardedNode_original (f C) (r C) σ hσ hq hd hq3 (A₀ i) C.1 (B₀ i) C.2
        (hA₀ i) (hB₀ i) c δ τ P hc hc9 hδ hτ).2 x
      dsimp only [rate]
      rw [relationMass_singleton_right, sum_uniformWeight]
      have he : (Finset.univ.filter (fun y => Incident x y)) ∩ B₀ i =
          (B₀ i).filter (fun y => Incident x y) := by ext y; simp [and_comm]
      rw [he]
      exact h) tree (Finset.univ,Finset.univ) j
  rw [eventMass_map_filter] at hh
  exact hh

theorem oriented_original_dual_cap
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (x : (ℙ K (Dual K V))) (tree : BinaryTree I) (j : Address tree) :
    eventMass (orientedPivotTreeLaw f r tree) (Finset.univ.filter (fun ω =>
      Excludes x ((orientedPivotCapsAt f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω
        (Finset.univ,Finset.univ) j).map Prod.fst))) ≤
      (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass Incident (uniformWeight (A₀ (label tree j))) (uniformWeight {x}) := by
  let Ω := fun _ : I => OrientedPivotTape f r
  let M := fun _ : I => OrientedPivotMessage f r
  let p := fun (_ : I) C => orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)
  let enc : ∀ i C t, Option (M i C t) := fun i C t =>
    orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ t
  let out : ∀ i C t, M i C t → _ := fun _ C t =>
    orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t
  let rate := fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) *
    relationMass Incident (uniformWeight (A₀ i)) (uniformWeight {x})
  have hn : ∀ i, 0≤rate i := fun i => mul_nonneg (by positivity)
    (relationMass_nonneg _ _ _ (uniformWeight_nonneg _) (uniformWeight_nonneg _))
  have hh := observe_event_bound Ω M (fun _ => orientedPivotLeft f r) (fun _ => orientedPivotRight f r)
    p enc out (fun o => Excludes x (o.map Prod.fst)) (by simp [Excludes]) rate hn
    (fun i C => by
      have h := (orientedGuardedNode_original (f C) (r C) σ hσ hq hd hq3 (A₀ i) C.1 (B₀ i) C.2
        (hA₀ i) (hB₀ i) c δ τ P hc hc9 hδ hτ).1 x
      dsimp only [rate]
      rw [relationMass_singleton_right, sum_uniformWeight]
      have he : (Finset.univ.filter (fun y => Incident y x)) ∩ A₀ i =
          (A₀ i).filter (fun y => Incident y x) := by ext y; simp [and_comm]
      rw [he]
      exact h) tree (Finset.univ,Finset.univ) j
  rw [eventMass_map_filter] at hh
  exact hh

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
