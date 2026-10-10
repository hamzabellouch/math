import OAI.Probability.InvariantIsing.Cavity.OffsetBlockPrior
import OAI.Probability.InvariantIsing.Fields.PriorMinimumIncrement
import OAI.Probability.InvariantIsing.Magnetic.RestrictedZeroTreeArrayLaw

namespace OAI

/-! A minimum at the next repeated-block dimension controls the genuine
base/cavity increment. Dimension casts do not impose a new model hypothesis. -/
noncomputable section
open MeasureTheory IsingPerceptron
namespace InvariantIsing

theorem offset_minimum_increment {m n K r : ℕ}
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N))
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (R : Finset (Spin r)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (uB : Fin (r+K*n) → ℝ) (vB : Fin m → ℝ)
    (uF : Fin (r+(K+1)*n) → ℝ) (vF : Fin m → ℝ)
    (huB : ∀ i, uB i ∈ Set.Icc (1 : ℝ) 2) (hvB : ∀ a, vB a ∈ Set.Icc (1 : ℝ) 2)
    (hminF : ∀ u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (μ (r+(K+1)*n))
        (restrictedZeroTreePrior (offsetBlockConstraint (K+1) R C)
          (offsetBlockConstraint_nonempty R hR C hC))
        (eig (r+(K+1)*n)) (c (r+(K+1)*n)) (I (r+(K+1)*n)) 1 (fun _ => 0) uF vF ≤
      priorPerturbationObjective (μ (r+(K+1)*n))
        (restrictedZeroTreePrior (offsetBlockConstraint (K+1) R C)
          (offsetBlockConstraint_nonempty R hR C hC))
        (eig (r+(K+1)*n)) (c (r+(K+1)*n)) (I (r+(K+1)*n)) 1 (fun _ => 0) u' v') :
    -((r+(K+1)*n : ℕ) : ℝ)*priorPerturbationObjective (μ (r+(K+1)*n))
        (restrictedZeroTreePrior (offsetBlockConstraint (K+1) R C)
          (offsetBlockConstraint_nonempty R hR C hC))
        (eig (r+(K+1)*n)) (c (r+(K+1)*n)) (I (r+(K+1)*n)) 1 (fun _ => 0) uF vF +
      ((r+K*n : ℕ) : ℝ)*priorPerturbationObjective (μ (r+K*n))
        (restrictedZeroTreePrior (offsetBlockConstraint K R C)
          (offsetBlockConstraint_nonempty R hR C hC))
        (eig (r+K*n)) (c (r+K*n)) (I (r+K*n)) 1 (fun _ => 0) uB vB ≥
    (((r+K*n+n : ℕ) : ℝ)*priorPerturbationPressureMean (μ (r+K*n+n))
      (restrictedZeroTreePrior (cavityProductSlice (offsetBlockConstraint K R C) C)
        (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC))
      (eig (r+K*n+n)) (c (r+K*n+n)) (I (r+K*n+n)) 1 (fun _ => 0)
      (fun i => cavityBaseAmplitude uB i) vB -
      ((r+K*n : ℕ) : ℝ)*priorPerturbationPressureMean (μ (r+K*n))
        (restrictedZeroTreePrior (offsetBlockConstraint K R C)
          (offsetBlockConstraint_nonempty R hR C hC))
        (eig (r+K*n)) (c (r+K*n)) (I (r+K*n)) 1 (fun _ => 0) uB vB) -
      (n : ℝ)*tensorMinimumPenalty uB vB -
      ((r+K*n+n : ℕ) : ℝ)*(1/4:ℝ)*(1/2:ℝ)^(r+K*n) := by
  let O := fun (N : ℕ) (S : Finset (Spin N)) (hS : S.Nonempty)
    (u : Fin N → ℝ) (v : Fin m → ℝ) =>
      priorPerturbationObjective (μ N) (restrictedZeroTreePrior S hS)
        (eig N) (c N) (I N) 1 (fun _ => 0) u v
  let value := O (r+(K+1)*n) (offsetBlockConstraint (K+1) R C)
    (offsetBlockConstraint_nonempty R hR C hC) uF vF
  let P := fun (N : ℕ) (S : Finset (Spin N)) => ∀ hS : S.Nonempty,
    ∃ (u : Fin N → ℝ) (v : Fin m → ℝ), O N S hS u v = value ∧
      ∀ u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
        (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) → O N S hS u v ≤ O N S hS u' v'
  have hP : P (r+(K+1)*n) (offsetBlockConstraint (K+1) R C) := by
    intro hS
    exact ⟨uF,vF,rfl,hminF⟩
  rw [offset_spin_family_succ P K R C] at hP
  obtain ⟨u,v,heq,hmin⟩ := hP
    (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC)
  have hi := prior_minimum_increment (μ (r+K*n+n)) (μ (r+K*n))
    (restrictedZeroTreePrior (cavityProductSlice (offsetBlockConstraint K R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC))
    (restrictedZeroTreePrior (offsetBlockConstraint K R C)
      (offsetBlockConstraint_nonempty R hR C hC))
    (eig (r+K*n+n)) (c (r+K*n+n)) (eig (r+K*n)) (c (r+K*n)) (I (r+K*n+n)) (I (r+K*n))
    1 (fun _ => 0) u v uB vB huB hvB hmin
  dsimp only [O, value] at heq
  dsimp only at hi
  rw [heq] at hi
  simpa only [Nat.succ_mul, Nat.add_assoc, Nat.cast_add, add_assoc] using hi

end InvariantIsing

end

end OAI
