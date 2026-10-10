import OAI.Probability.InvariantIsing.Cavity.ConsecutiveBlockTransport
import OAI.Probability.InvariantIsing.Fields.PriorMinimumIncrement
import OAI.Probability.InvariantIsing.Magnetic.RestrictedZeroTreeArrayLaw

namespace OAI

/-! A minimum at the next repeated-block dimension controls the genuine
base/cavity increment. Dimension casts do not impose a new model hypothesis. -/
noncomputable section
open MeasureTheory IsingPerceptron
namespace InvariantIsing

theorem consecutive_minimum_increment {m n K : ℕ}
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N))
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (uB : Fin (K*n) → ℝ) (vB : Fin m → ℝ)
    (uF : Fin ((K+1)*n) → ℝ) (vF : Fin m → ℝ)
    (huB : ∀ i, uB i ∈ Set.Icc (1 : ℝ) 2) (hvB : ∀ a, vB a ∈ Set.Icc (1 : ℝ) 2)
    (hminF : ∀ u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (μ ((K+1)*n))
        (restrictedZeroTreePrior (consecutiveBlockConstraint n (K+1) C)
          (consecutiveBlockConstraint_nonempty C hC))
        (eig ((K+1)*n)) (c ((K+1)*n)) (I ((K+1)*n)) 1 (fun _ => 0) uF vF ≤
      priorPerturbationObjective (μ ((K+1)*n))
        (restrictedZeroTreePrior (consecutiveBlockConstraint n (K+1) C)
          (consecutiveBlockConstraint_nonempty C hC))
        (eig ((K+1)*n)) (c ((K+1)*n)) (I ((K+1)*n)) 1 (fun _ => 0) u' v') :
    -(((K+1)*n : ℕ) : ℝ)*priorPerturbationObjective (μ ((K+1)*n))
        (restrictedZeroTreePrior (consecutiveBlockConstraint n (K+1) C)
          (consecutiveBlockConstraint_nonempty C hC))
        (eig ((K+1)*n)) (c ((K+1)*n)) (I ((K+1)*n)) 1 (fun _ => 0) uF vF +
      ((K*n : ℕ) : ℝ)*priorPerturbationObjective (μ (K*n))
        (restrictedZeroTreePrior (consecutiveBlockConstraint n K C)
          (consecutiveBlockConstraint_nonempty C hC))
        (eig (K*n)) (c (K*n)) (I (K*n)) 1 (fun _ => 0) uB vB ≥
    (((K*n+n : ℕ) : ℝ)*priorPerturbationPressureMean (μ (K*n+n))
      (restrictedZeroTreePrior (cavityProductSlice (consecutiveBlockConstraint n K C) C)
        (cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC))
      (eig (K*n+n)) (c (K*n+n)) (I (K*n+n)) 1 (fun _ => 0)
      (fun i => cavityBaseAmplitude uB i) vB -
      ((K*n : ℕ) : ℝ)*priorPerturbationPressureMean (μ (K*n))
        (restrictedZeroTreePrior (consecutiveBlockConstraint n K C)
          (consecutiveBlockConstraint_nonempty C hC))
        (eig (K*n)) (c (K*n)) (I (K*n)) 1 (fun _ => 0) uB vB) -
      (n : ℝ)*tensorMinimumPenalty uB vB -
      ((K*n+n : ℕ) : ℝ)*(1/4:ℝ)*(1/2:ℝ)^(K*n) := by
  let O := fun (N : ℕ) (S : Finset (Spin N)) (hS : S.Nonempty)
    (u : Fin N → ℝ) (v : Fin m → ℝ) =>
      priorPerturbationObjective (μ N) (restrictedZeroTreePrior S hS)
        (eig N) (c N) (I N) 1 (fun _ => 0) u v
  let value := O ((K+1)*n) (consecutiveBlockConstraint n (K+1) C)
    (consecutiveBlockConstraint_nonempty C hC) uF vF
  let P := fun (N : ℕ) (S : Finset (Spin N)) => ∀ hS : S.Nonempty,
    ∃ (u : Fin N → ℝ) (v : Fin m → ℝ), O N S hS u v = value ∧
      ∀ u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
        (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) → O N S hS u v ≤ O N S hS u' v'
  have hP : P ((K+1)*n) (consecutiveBlockConstraint n (K+1) C) := by
    intro hS
    exact ⟨uF,vF,rfl,hminF⟩
  rw [consecutive_spin_family_succ P n K C] at hP
  obtain ⟨u,v,heq,hmin⟩ := hP
    (cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC)
  have hi := prior_minimum_increment (μ (K*n+n)) (μ (K*n))
    (restrictedZeroTreePrior (cavityProductSlice (consecutiveBlockConstraint n K C) C)
      (cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC))
    (restrictedZeroTreePrior (consecutiveBlockConstraint n K C)
      (consecutiveBlockConstraint_nonempty C hC))
    (eig (K*n+n)) (c (K*n+n)) (eig (K*n)) (c (K*n)) (I (K*n+n)) (I (K*n))
    1 (fun _ => 0) u v uB vB huB hvB hmin
  dsimp only [O, value] at heq
  dsimp only at hi
  rw [heq] at hi
  simpa only [Nat.succ_mul, Nat.cast_add] using hi

end InvariantIsing

end

end OAI
