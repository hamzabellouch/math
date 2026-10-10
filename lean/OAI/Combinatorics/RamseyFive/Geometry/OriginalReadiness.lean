import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.LevelTreeTrims
import OAI.Combinatorics.RamseyFive.Entropy.LevelDensity

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) allPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma not_original_ready_iff (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA : A₀.Nonempty) (hB : B₀.Nonempty) (δ τ : ℝ) :
    ¬OriginalNodeReady A₀ UA B₀ UB δ τ ↔
      ((A₀∩UA).card:ℝ) < δ*A₀.card ∨ ((B₀∩UB).card:ℝ) < δ*B₀.card ∨
        τ < (Nat.card K:ℝ)*relationMass Incident (uniformWeight A₀) (uniformWeight B₀) := by
  rw [OriginalNodeReady, incidences, scaled_uniform_density_iff Incident A₀ B₀ hA hB]
  simp only [not_and_or, not_le]

theorem original_not_ready_mass {W : Type*} [Fintype W] (p : Law W)
    (A₀ : Finset (ℙ K V)) (B₀ : Finset (ℙ K (Dual K V)))
    (hA : A₀.Nonempty) (hB : B₀.Nonempty) (δ τ : ℝ)
    (ctx : W → Option (PivotContext K V)) :
    eventMass p (Finset.univ.filter (fun ω => ∃ C,
      ctx ω = some C ∧ ¬OriginalNodeReady A₀ C.1 B₀ C.2 δ τ)) ≤
      eventMass p (Finset.univ.filter (fun ω => ∃ C,
        ctx ω = some C ∧ ((A₀∩C.1).card:ℝ) < δ*A₀.card)) +
      eventMass p (Finset.univ.filter (fun ω => ∃ C,
        ctx ω = some C ∧ ((B₀∩C.2).card:ℝ) < δ*B₀.card)) +
      if τ < (Nat.card K:ℝ)*relationMass Incident (uniformWeight A₀) (uniformWeight B₀) then 1 else 0 := by
  let P := fun ω => ∃ C, ctx ω = some C ∧ ((A₀∩C.1).card:ℝ) < δ*A₀.card
  let Q := fun ω => ∃ C, ctx ω = some C ∧ ((B₀∩C.2).card:ℝ) < δ*B₀.card
  let E := τ < (Nat.card K:ℝ)*relationMass Incident (uniformWeight A₀) (uniformWeight B₀)
  have hd : eventMass p (Finset.univ.filter (fun _ : W => E)) = if E then 1 else 0 := by
    by_cases h : E <;> simp [h, eventMass, p.sum_one]
  have hs : ∀ ω, (∃ C, ctx ω = some C ∧ ¬OriginalNodeReady A₀ C.1 B₀ C.2 δ τ) → (P ω ∨ Q ω) ∨ E := by
    rintro ω ⟨C,hC,hr⟩
    rcases (not_original_ready_iff A₀ C.1 B₀ C.2 hA hB δ τ).mp hr with ha | hb | he
    · exact Or.inl (Or.inl ⟨C,hC,ha⟩)
    · exact Or.inl (Or.inr ⟨C,hC,hb⟩)
    · exact Or.inr he
  calc
    _ ≤ eventMass p (Finset.univ.filter (fun ω => (P ω ∨ Q ω) ∨ E)) := eventMass_filter_mono _ _ _ hs
    _ ≤ eventMass p (Finset.univ.filter (fun ω => P ω ∨ Q ω)) + eventMass p (Finset.univ.filter (fun _ : W => E)) := by
      convert eventMass_filter_union p (fun ω => P ω ∨ Q ω) (fun _ : W => E) using 1; congr
    _ ≤ _ := by rw [hd]; convert add_le_add (eventMass_filter_union p P Q) (le_refl (if E then (1:ℝ) else 0)) using 1; congr
end
end

open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) levelReadinessPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type} [Fintype I] [DecidableEq I]
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

theorem oriented_level_not_ready
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a) ≤ L*p i a)
    (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b) ≤ L*q i b)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2) (hτpos : 0<τ)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => ∃ C,
        orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j = some C ∧
        ¬OriginalNodeReady (X (label tree j) (z.1 (label tree j))) C.1
          (Y (label tree j) (z.2 (label tree j))) C.2 (9/10) τ))) ≤
      10 * pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) * L^2 *
        relationMass Incident (p (label tree j)) (q i)) (fun _ => 0) tree j +
      10 * pathBudget (fun _ => 0) (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) * L^2 *
        relationMass Incident (p i) (q (label tree j))) tree j +
      ((Nat.card K:ℝ)/τ)*L^2*relationMass Incident (p (label tree j)) (q (label tree j)) := by
  let i := label tree j
  let ctx := fun (z : (∀ i, A i) × (∀ i, B i)) (ω : OrientedPivotTreeTape f r tree) =>
    orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
      (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j
  let EA := fun (z : (∀ i, A i) × (∀ i, B i)) => eventMass (orientedPivotTreeLaw f r tree)
    (Finset.univ.filter (fun ω => ∃ C, ctx z ω = some C ∧ ((X i (z.1 i)∩C.1).card:ℝ) < (9/10:ℝ)*(X i (z.1 i)).card))
  let EB := fun (z : (∀ i, A i) × (∀ i, B i)) => eventMass (orientedPivotTreeLaw f r tree)
    (Finset.univ.filter (fun ω => ∃ C, ctx z ω = some C ∧ ((Y i (z.2 i)∩C.2).card:ℝ) < (9/10:ℝ)*(Y i (z.2 i)).card))
  let ED := fun (z : (∀ i, A i) × (∀ i, B i)) =>
    τ < (Nat.card K:ℝ)*relationMass Incident (uniformWeight (X i (z.1 i))) (uniformWeight (Y i (z.2 i)))
  have ha := oriented_level_point_trim f r σ hσ hq hd hq3 μ ν X Y hX hY p q L hL hμ hν c δ τ P hc hc9 hδ hτ tree j
  have hb := oriented_level_dual_trim f r σ hσ hq hd hq3 μ ν X Y hX hY p q L hL hμ hν c δ τ P hc hc9 hδ hτ tree j
  have hdens := original_level_density_rejection μ ν i i Incident (X i) (Y i) (p i) (q i) L hL (hμ i) (hν i)
    (Nat.card K) τ (Nat.cast_nonneg _) hτpos
  have he : (∑ z, originalLevelLaw μ ν z * (if ED z then 1 else 0)) = eventMass (originalLevelLaw μ ν) (Finset.univ.filter ED) := by
    simp only [eventMass, Finset.sum_filter, mul_ite, mul_one, mul_zero]
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z * (EA z + EB z + if ED z then 1 else 0) := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (original_not_ready_mass (orientedPivotTreeLaw f r tree)
        (X i (z.1 i)) (Y i (z.2 i)) (hX i _) (hY i _) (9/10) τ (ctx z)) ((originalLevelLaw μ ν).nonneg z)
    _ = (∑ z, originalLevelLaw μ ν z * EA z) + (∑ z, originalLevelLaw μ ν z * EB z) +
        eventMass (originalLevelLaw μ ν) (Finset.univ.filter ED) := by simp_rw [mul_add, Finset.sum_add_distrib]; rw [he]
    _ ≤ _ := by
      apply add_le_add
      · apply add_le_add
        · convert ha using 1; congr
          funext z
          dsimp only [EA,ctx,i]
          congr 2
          ext ω
          simp only [Finset.mem_filter]
        · convert hb using 1; congr
          funext z
          dsimp only [EB,ctx,i]
          congr 2
          ext ω
          simp only [Finset.mem_filter]
      · convert hdens using 1
end

end SharpRamseyFive.ProjectiveIncidence

end OAI
