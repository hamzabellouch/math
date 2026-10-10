import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.TreeTrims

namespace OAI

namespace SharpRamseyFive.ReverseCap
open scoped Classical
variable {α : Type*}
lemma singleton_trim_iff (a : α) (U : Finset α) :
    (({a} ∩ U).card:ℝ) < (9/10:ℝ)*({a}:Finset α).card ↔ a∉U := by
  by_cases h : a∈U
  · simp [Finset.singleton_inter_of_mem h, h]
    norm_num
  · simp [Finset.singleton_inter_of_notMem h, h]
end SharpRamseyFive.ReverseCap
namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) actualTargetTrimsPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type}
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

theorem oriented_original_point_target
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (a : ℙ K V) (tree : BinaryTree I) (j : Address tree) :
    eventMass (orientedPivotTreeLaw f r tree) (Finset.univ.filter (fun ω => ∃ C,
      orientedPivotContextAt f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω
        (Finset.univ,Finset.univ) j = some C ∧ a∉C.1)) ≤
      10 * pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass (fun b a => Incident a b) (uniformWeight (B₀ i)) (uniformWeight {a}))
        (fun _ => 0) tree j := by
  have h := oriented_original_point_trim f r σ hσ hq hd hq3 A₀ B₀ hA₀ hB₀ c δ τ P hc hc9 hδ hτ {a} tree j
  simpa only [singleton_trim_iff] using h

theorem oriented_original_dual_target
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ : I → Finset (ℙ K V)) (B₀ : I → Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i, (A₀ i).Nonempty) (hB₀ : ∀ i, (B₀ i).Nonempty)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (b : ℙ K (Dual K V)) (tree : BinaryTree I) (j : Address tree) :
    eventMass (orientedPivotTreeLaw f r tree) (Finset.univ.filter (fun ω => ∃ C,
      orientedPivotContextAt f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω
        (Finset.univ,Finset.univ) j = some C ∧ b∉C.2)) ≤
      10 * pathBudget (fun _ => 0) (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) *
        relationMass Incident (uniformWeight (A₀ i)) (uniformWeight {b})) tree j := by
  have h := oriented_original_dual_trim f r σ hσ hq hd hq3 A₀ B₀ hA₀ hB₀ c δ τ P hc hc9 hδ hτ {b} tree j
  simpa only [singleton_trim_iff] using h
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
