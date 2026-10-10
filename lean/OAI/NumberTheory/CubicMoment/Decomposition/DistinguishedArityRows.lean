import OAI.NumberTheory.CubicMoment.Estimates.BoundedDistinguishedCoefficient
import OAI.NumberTheory.CubicMoment.Estimates.CentralStoppingDecomposition

namespace OAI

/-! Finite fixed-arity reconstruction of the original distinguished rows.
Only squarefreeness already forced by the original product support is used
when passing to the independent prime convolutions. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem distinguished_rows_by_arity {ξ C : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hC : 0 < C)
    {ψ : ℝ → ℝ} (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0) :
    ∃ k : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (R S : Finset Eisenstein) (K : Eisenstein → ℂ),
      (∀ r ∈ R, primary r ∧ norm r ≤ C*X) → (∀ n ∈ S, Squarefree n) →
      (∑ r ∈ R, distinguishedSubsetWeight ψ (X^ξ) (X^(2/5:ℝ)) r*
        ∑ u ∈ primaryProductSlice S (C*X) r, (roughProduct ψ (X^ξ) u:ℂ)*K (r*u)) =
      ∑ i ∈ Finset.range k, ∑ r ∈ R,
        distinguishedTupleCoefficient (fun _ : Fin i => primeCutoff (C*X))
          (fun _ _ => 1) ψ (X^ξ) (X^(2/5:ℝ)) r*
        ∑ u ∈ primaryProductSlice S (C*X) r, (roughProduct ψ (X^ξ) u:ℂ)*K (r*u) := by
  obtain ⟨k,hbound⟩ := eventually_distinguished_coefficient_tuples hξ hξz hC hψone hψzero
  refine ⟨k,?_⟩
  filter_upwards [hbound] with X hX
  intro R S K hR hS
  calc
    _ = ∑ r ∈ R,
        (∑ i ∈ Finset.range k, distinguishedTupleCoefficient
          (fun _ : Fin i => primeCutoff (C*X)) (fun _ _ => 1) ψ (X^ξ) (X^(2/5:ℝ)) r)*
        ∑ u ∈ primaryProductSlice S (C*X) r, (roughProduct ψ (X^ξ) u:ℂ)*K (r*u) := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hs : Squarefree r
      · rw [hX r (hR r hr).1 hs (hR r hr).2]
      · have hz : (∑ u ∈ primaryProductSlice S (C*X) r,
            (roughProduct ψ (X^ξ) u:ℂ)*K (r*u)) = 0 := by
          apply Finset.sum_eq_zero
          intro u hu
          exact (hs (hS (r*u) (Finset.mem_filter.mp hu).2).of_mul_left).elim
        rw [hz,mul_zero,mul_zero]
    _ = _ := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]

def distinguishedLargeArityLow (i : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ r ∈ (centralPrimaryFactors X).filter (fun r => ¬norm r < X^(38/100:ℝ)),
    distinguishedTupleCoefficient
      (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
      (fun _ _ => 1) primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) r*
    ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) r,
      (roughProduct primeDetectorCutoff (X^ξ) u:ℂ)*
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (r*u)

theorem distinguishedLargeLow_by_arity {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ k : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (Ct : ℕ) (H : ℝ),
      distinguishedLargeLow ℓ ξ Ct H X =
        ∑ i ∈ Finset.range k, distinguishedLargeArityLow i ℓ ξ Ct H X := by
  obtain ⟨k,hbound⟩ := distinguished_rows_by_arity hξ hξz (Real.exp_pos primeProductWeights.radius)
    (fun _ _ hx => primeDetectorCutoff_one hx) (fun _ hx => primeDetectorCutoff_zero hx)
  refine ⟨k,?_⟩
  filter_upwards [hbound] with X hX
  intro ℓ Ct H
  exact hX ((centralPrimaryFactors X).filter (fun r => ¬norm r < X^(38/100:ℝ)))
    (centralProductEnvelope X)
    (centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X)
    (fun r hr => mem_primaryElementBall.mp (Finset.mem_filter.mp hr).1)
    (fun n hn => (centralProductEnvelope_spec hn).2.1)

end CubicFirstMoment

end

end OAI
