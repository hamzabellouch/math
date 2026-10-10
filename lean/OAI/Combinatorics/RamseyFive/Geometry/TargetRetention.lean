import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.TargetCoherence
import OAI.Combinatorics.RamseyFive.Entropy.IndependentTargetLoss
import OAI.Combinatorics.RamseyFive.Geometry.LevelTargetBounds

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) actualTargetRetentionPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I Ω : Type} [Fintype I] [DecidableEq I] [Fintype Ω]
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

theorem oriented_actual_target_loss
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
    (L : ℝ)
    (hflatA : ∀ i a, (∑ s, μ i s*uniformWeight (X i s) a) ≤ L*p i a)
    (hflatB : ∀ i b, (∑ s, ν i s*uniformWeight (Y i s) b) ≤ L*q i b)
    (γ : Law Ω) (a : Ω → ℙ K V) (b : Ω → ℙ K (Dual K V))
    (goodA : ℙ K V → Prop) (goodB : ℙ K (Dual K V) → Prop)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    let ctx := fun z : ((∀ i, A i) × (∀ i, B i)) × OrientedPivotTreeTape f r tree =>
      orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1.1 i)) (fun i => Y i (z.1.2 i))
        (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree z.2 (Finset.univ,Finset.univ) j
    let caps := fun z : ((∀ i, A i) × (∀ i, B i)) × OrientedPivotTreeTape f r tree =>
      orientedPivotCapsAt f r σ hσ hq hd.le (fun i => X i (z.1.1 i)) (fun i => Y i (z.1.2 i))
        (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree z.2 (Finset.univ,Finset.univ) j
    let gA := fun x => if goodA x then map γ a x else 0
    let gB := fun y => if goodB y then map γ b y else 0
    let C₀ := 50*(Nat.card K:ℝ)/(9*(c*δ))
    eventMass (adaptiveLaw γ (fun _ => adaptiveLaw (originalLevelLaw μ ν)
      (fun _ => orientedPivotTreeLaw f r tree))) (Finset.univ.filter
        (fun z => ¬TargetCovered (ctx z.2) (caps z.2) (a z.1) (b z.1))) ≤
      eventMass γ (Finset.univ.filter (fun x => ¬goodA (a x))) +
      eventMass γ (Finset.univ.filter (fun x => ¬goodB (b x))) +
      (∑ z, originalLevelLaw μ ν z*eventMass (orientedPivotTreeLaw f r tree)
        (Finset.univ.filter (fun ω => orientedPivotSuccessAt f r σ hσ hq hd.le
          (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
          c δ τ P hδ tree ω (Finset.univ,Finset.univ) j=none))) +
      10*pathBudget (fun i => C₀*L*relationMass Incident gA (q i)) (fun _ => 0) tree j +
      10*pathBudget (fun _ => 0) (fun i => C₀*L*relationMass Incident (p i) gB) tree j +
      C₀*L*relationMass Incident gA (q (label tree j)) +
      C₀*L*relationMass Incident (p (label tree j)) gB := by
  dsimp only
  let ctx := fun z : ((∀ i, A i) × (∀ i, B i)) × OrientedPivotTreeTape f r tree =>
    orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1.1 i)) (fun i => Y i (z.1.2 i))
      (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree z.2 (Finset.univ,Finset.univ) j
  let caps := fun z : ((∀ i, A i) × (∀ i, B i)) × OrientedPivotTreeTape f r tree =>
    orientedPivotCapsAt f r σ hσ hq hd.le (fun i => X i (z.1.1 i)) (fun i => Y i (z.1.2 i))
      (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree z.2 (Finset.univ,Finset.univ) j
  let gA := fun x => if goodA x then map γ a x else 0
  let gB := fun y => if goodB y then map γ b y else 0
  have hgA : ∀ x, 0≤gA x := by intro x; dsimp [gA]; split_ifs; exact (map γ a).nonneg x; rfl
  have hgB : ∀ y, 0≤gB y := by intro y; dsimp [gB]; split_ifs; exact (map γ b).nonneg y; rfl
  have hcoh : ∀ z, caps z≠none → ctx z≠none := by
    intro z
    exact oriented_caps_context_coherent f r σ hσ hq hd.le _ _ _ _ c δ τ P hδ tree z.2 _ j
  have h := independent_target_loss γ
    (adaptiveLaw (originalLevelLaw μ ν) (fun _ => orientedPivotTreeLaw f r tree))
    a b goodA goodB ctx caps hcoh
  have hn : eventMass (adaptiveLaw (originalLevelLaw μ ν) (fun _ => orientedPivotTreeLaw f r tree))
      (Finset.univ.filter (fun z => caps z=none)) =
      ∑ z, originalLevelLaw μ ν z*eventMass (orientedPivotTreeLaw f r tree)
        (Finset.univ.filter (fun ω => orientedPivotSuccessAt f r σ hσ hq hd.le
          (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
          c δ τ P hδ tree ω (Finset.univ,Finset.univ) j=none)) := by
    rw [independent_target_event_general]
    apply Finset.sum_congr rfl
    intro z _
    congr 2
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact oriented_caps_none_iff f r σ hσ hq hd.le _ _ _ _ c δ τ P hδ tree ω _ j
  rw [hn] at h
  dsimp only [ctx,caps] at h
  rw [independent_weighted_event, independent_weighted_event,
    independent_weighted_event, independent_weighted_event] at h
  have h1 := oriented_level_point_target_trim f r σ hσ hq hd hq3 μ ν X Y hX hY q gA hgA L hflatB c δ τ P hc hc9 hδ hτ tree j
  have h2 := oriented_level_dual_target_trim f r σ hσ hq hd hq3 μ ν X Y hX hY p gB hgB L hflatA c δ τ P hc hc9 hδ hτ tree j
  have h3 := oriented_level_point_target_cap f r σ hσ hq hd hq3 μ ν X Y hX hY q gA hgA L hflatB c δ τ P hc hc9 hδ hτ tree j
  have h4 := oriented_level_dual_target_cap f r σ hσ hq hd hq3 μ ν X Y hX hY p gB hgB L hflatA c δ τ P hc hc9 hδ hτ tree j
  exact h.trans (add_le_add (add_le_add (add_le_add (add_le_add_right h1 _) h2) h3) h4)
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
