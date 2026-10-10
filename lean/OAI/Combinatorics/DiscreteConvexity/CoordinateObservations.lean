import OAI.Combinatorics.DiscreteConvexity.Bernoulli
import OAI.Combinatorics.DiscreteConvexity.ProductProbability

namespace OAI

/-!
# Boolean observations of finite product laws

Independent Boolean observations with common success probability have the
Bernoulli law on subsets, both on individual atoms and on arbitrary families.
-/

open scoped BigOperators
noncomputable section

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]
  {Ω : α → Type*} [∀ i, Fintype (Ω i)]

/-- A specified set of successful coordinate observations has its Bernoulli mass. -/
theorem prob_pi_cubeSet_eq_mass (μ : ∀ i, FiniteLaw (Ω i))
    (obs : ∀ i, Ω i → Bool) (p : ℝ)
    (hobs : ∀ i, (μ i).prob (fun w => obs i w = true) = p) (s : Finset α) :
    (FiniteLaw.pi μ).prob (fun ω => cubeSet (fun i => obs i (ω i)) = s) =
      bernoulliMass p s := by
  classical
  have hcoord (i : α) :
      (μ i).prob (fun w => (obs i w = true ↔ i ∈ s)) =
        if i ∈ s then p else 1 - p := by
    by_cases hi : i ∈ s
    · simpa [hi] using hobs i
    · simpa [hi, hobs i] using (μ i).prob_compl (fun w => obs i w = true)
  calc
    (FiniteLaw.pi μ).prob (fun ω => cubeSet (fun i => obs i (ω i)) = s) =
        (FiniteLaw.pi μ).prob (fun ω => ∀ i, obs i (ω i) = true ↔ i ∈ s) := by
      congr 1
      funext ω
      apply propext
      simp only [Finset.ext_iff, mem_cubeSet]
    _ = ∏ i, (μ i).prob (fun w => (obs i w = true ↔ i ∈ s)) :=
      FiniteLaw.prob_pi μ (fun i w => (obs i w = true ↔ i ∈ s))
    _ = ∏ i, if i ∈ s then p else 1 - p := by
      apply Finset.prod_congr rfl
      intro i _
      exact hcoord i
    _ = bernoulliMass p s := bernoulliWeight_eq_mass p s

/-- Membership of the observed set in a family has exactly its Bernoulli measure. -/
theorem prob_pi_cubeSet_mem_family (μ : ∀ i, FiniteLaw (Ω i))
    (obs : ∀ i, Ω i → Bool) (p : ℝ)
    (hobs : ∀ i, (μ i).prob (fun w => obs i w = true) = p) (D : Family α) :
    (FiniteLaw.pi μ).prob (fun ω => cubeSet (fun i => obs i (ω i)) ∈ D) =
      familyMeasure p D := by
  classical
  let f : (∀ i, Ω i) → Finset α := fun ω => cubeSet (fun i => obs i (ω i))
  calc
    (FiniteLaw.pi μ).prob (fun ω => cubeSet (fun i => obs i (ω i)) ∈ D) =
        ((FiniteLaw.pi μ).map f).prob (fun s => s ∈ D) :=
      (FiniteLaw.prob_map (FiniteLaw.pi μ) f (fun s => s ∈ D)).symm
    _ = ∑ s ∈ D, ((FiniteLaw.pi μ).map f).weight s := by
      calc
        ((FiniteLaw.pi μ).map f).prob (fun s => s ∈ D) =
            ∑ s : Finset α, if s ∈ D then ((FiniteLaw.pi μ).map f).weight s else 0 := by
          unfold FiniteLaw.prob
          apply Finset.sum_congr rfl
          intro s _
          by_cases hs : s ∈ D <;> simp [hs]
        _ = _ := Finset.sum_ite_mem_eq D ((FiniteLaw.pi μ).map f).weight
    _ = ∑ s ∈ D, bernoulliMass p s := by
      apply Finset.sum_congr rfl
      intro s _
      rw [FiniteLaw.map_weight_eq_prob]
      exact prob_pi_cubeSet_eq_mass μ obs p hobs s
    _ = familyMeasure p D := rfl

end TalagrandDiscreteConvexity

end

end OAI
