import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.TargetCaps
import OAI.Combinatorics.RamseyFive.Trees.TargetTrims
import OAI.Combinatorics.RamseyFive.Entropy.TargetAverage

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) levelTargetBoundsPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type} [Fintype I] [DecidableEq I]
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

theorem oriented_level_point_target_trim
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K (Dual K V))) (g : ℙ K V → ℝ) (hg : ∀ a, 0≤g a)
    (L : ℝ) (hflat : ∀ i a, (∑ s, ν i s*uniformWeight (Y i s) a) ≤ L*p i a)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * (∑ a, g a*eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => ∃ C,
        orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j = some C ∧ a∉C.1)))) ≤
      10*pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ)))*L*relationMass Incident (g) (p i)) (fun _ => 0) tree j := by
  let C₀ : ℝ := 50*(Nat.card K:ℝ)/(9*(c*δ))
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  let ρ := fun (z : (∀ i, A i) × (∀ i, B i)) a i => C₀ * relationMass
    (fun b a => Incident a b) (uniformWeight (Y i (z.2 i))) (uniformWeight {a})
  have hpoint (z : (∀ i, A i) × (∀ i, B i)) (a : ℙ K V) :=
    oriented_original_point_target f r σ hσ hq hd hq3
      (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
      c δ τ P hc hc9 hδ hτ a tree j
  have hm (i : I) : (∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a i)) ≤
      C₀*L*relationMass Incident g (p i) :=
    original_target_mean_point μ ν i Incident (Y i) g (p i) C₀ L hC₀ hg (hflat i)
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z*(∑ a, g a*(10*pathBudget (ρ z a) (fun _ => 0) tree j)) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpoint z a) (hg a))
        ((originalLevelLaw μ ν).nonneg z)
    _ = 10*pathBudget (fun i => ∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a i)) (fun _ => 0) tree j := by
      simpa only [mul_zero, Finset.sum_const_zero] using
        mean_two_pathBudget_scaled (originalLevelLaw μ ν) g ρ (fun _ _ _ => 0) 10 tree j
    _ ≤ _ := mul_le_mul_of_nonneg_left (pathBudget_mono _ _ _ _
      hm (fun _ => le_refl 0) tree j) (by norm_num)

theorem oriented_level_point_target_cap
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K (Dual K V))) (g : ℙ K V → ℝ) (hg : ∀ a, 0≤g a)
    (L : ℝ) (hflat : ∀ i a, (∑ s, ν i s*uniformWeight (Y i s) a) ≤ L*p i a)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * (∑ a, g a*eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => Excludes a ((orientedPivotCapsAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j).map Prod.snd))))) ≤
      (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ)))*L*relationMass Incident (g) (p i)) (label tree j) := by
  let C₀ : ℝ := 50*(Nat.card K:ℝ)/(9*(c*δ))
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  let ρ := fun (z : (∀ i, A i) × (∀ i, B i)) a i => C₀ * relationMass
    (fun b a => Incident a b) (uniformWeight (Y i (z.2 i))) (uniformWeight {a})
  have hpoint (z : (∀ i, A i) × (∀ i, B i)) (a : ℙ K V) :=
    oriented_original_point_cap f r σ hσ hq hd hq3
      (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
      c δ τ P hc hc9 hδ hτ a tree j
  have hm (i : I) : (∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a i)) ≤
      C₀*L*relationMass Incident g (p i) :=
    original_target_mean_point μ ν i Incident (Y i) g (p i) C₀ L hC₀ hg (hflat i)
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a (label tree j)) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpoint z a) (hg a))
        ((originalLevelLaw μ ν).nonneg z)
    _ ≤ _ := hm (label tree j)

theorem oriented_level_dual_target_trim
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (g : ℙ K (Dual K V) → ℝ) (hg : ∀ a, 0≤g a)
    (L : ℝ) (hflat : ∀ i a, (∑ s, μ i s*uniformWeight (X i s) a) ≤ L*p i a)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * (∑ a, g a*eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => ∃ C,
        orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j = some C ∧ a∉C.2)))) ≤
      10*pathBudget (fun _ => 0) (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ)))*L*relationMass Incident (p i) (g)) tree j := by
  let C₀ : ℝ := 50*(Nat.card K:ℝ)/(9*(c*δ))
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  let ρ := fun (z : (∀ i, A i) × (∀ i, B i)) a i => C₀ * relationMass
    Incident (uniformWeight (X i (z.1 i))) (uniformWeight {a})
  have hpoint (z : (∀ i, A i) × (∀ i, B i)) (a : ℙ K (Dual K V)) :=
    oriented_original_dual_target f r σ hσ hq hd hq3
      (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
      c δ τ P hc hc9 hδ hτ a tree j
  have hm (i : I) : (∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a i)) ≤
      C₀*L*relationMass Incident (p i) g :=
    original_target_mean_dual μ ν i Incident (X i) (p i) g C₀ L hC₀ hg (hflat i)
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z*(∑ a, g a*(10*pathBudget (fun _ => 0) (ρ z a) tree j)) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpoint z a) (hg a))
        ((originalLevelLaw μ ν).nonneg z)
    _ = 10*pathBudget (fun _ => 0) (fun i => ∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a i)) tree j := by
      simpa only [mul_zero, Finset.sum_const_zero] using
        mean_two_pathBudget_scaled (originalLevelLaw μ ν) g (fun _ _ _ => 0) ρ 10 tree j
    _ ≤ _ := mul_le_mul_of_nonneg_left (pathBudget_mono _ _ _ _
      (fun _ => le_refl 0) hm tree j) (by norm_num)

theorem oriented_level_dual_target_cap
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (g : ℙ K (Dual K V) → ℝ) (hg : ∀ a, 0≤g a)
    (L : ℝ) (hflat : ∀ i a, (∑ s, μ i s*uniformWeight (X i s) a) ≤ L*p i a)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * (∑ a, g a*eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => Excludes a ((orientedPivotCapsAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j).map Prod.fst))))) ≤
      (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ)))*L*relationMass Incident (p i) (g)) (label tree j) := by
  let C₀ : ℝ := 50*(Nat.card K:ℝ)/(9*(c*δ))
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  let ρ := fun (z : (∀ i, A i) × (∀ i, B i)) a i => C₀ * relationMass
    Incident (uniformWeight (X i (z.1 i))) (uniformWeight {a})
  have hpoint (z : (∀ i, A i) × (∀ i, B i)) (a : ℙ K (Dual K V)) :=
    oriented_original_dual_cap f r σ hσ hq hd hq3
      (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
      c δ τ P hc hc9 hδ hτ a tree j
  have hm (i : I) : (∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a i)) ≤
      C₀*L*relationMass Incident (p i) g :=
    original_target_mean_dual μ ν i Incident (X i) (p i) g C₀ L hC₀ hg (hflat i)
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z*(∑ a, g a*ρ z a (label tree j)) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpoint z a) (hg a))
        ((originalLevelLaw μ ν).nonneg z)
    _ ≤ _ := hm (label tree j)
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
