import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedArityRows
import OAI.NumberTheory.CubicMoment.Estimates.RoughRemainderArity

namespace OAI

/-! Both sets of prime factors in the large distinguished rows are
of fixed, bounded arity. Original squarefreeness and product support are
kept inside the sum; no independent-tuple approximation is used. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem rough_slice_by_arity {ξ C : ℝ} (hξ : 0 < ξ) (hC : 0 < C)
    {ψ : ℝ → ℝ} (hψ : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1) :
    ∃ k : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (S : Finset Eisenstein)
      (r : Eisenstein) (K : Eisenstein → ℂ),
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ C*X) →
      (∑ u ∈ primaryProductSlice S (C*X) r, (roughProduct ψ (X^ξ) u:ℂ)*K (r*u)) =
        ∑ j ∈ Finset.range k, ∑ u ∈ primaryProductSlice S (C*X) r,
          roughTupleCoefficient j (C*X) ψ (X^ξ) u*K (r*u) := by
  obtain ⟨k,hbound⟩ := eventually_rough_coefficient_tuples hξ hC hψ
  refine ⟨k,?_⟩
  filter_upwards [hbound] with X hX
  intro S r K hS
  calc
    _ = ∑ u ∈ primaryProductSlice S (C*X) r,
        (∑ j ∈ Finset.range k, roughTupleCoefficient j (C*X) ψ (X^ξ) u)*K (r*u) := by
      apply Finset.sum_congr rfl
      intro u hu
      obtain ⟨hp,hs,hn⟩ := primaryProductSlice_support S (C*X) hS r u hu
      rw [hX u hp hs hn]
    _ = _ := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]

def distinguishedDoubleArityLow (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ r ∈ (centralPrimaryFactors X).filter (fun r => ¬norm r < X^(38/100:ℝ)),
    distinguishedTupleCoefficient
      (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
      (fun _ _ => 1) primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) r*
    ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) r,
      roughTupleCoefficient j (Real.exp primeProductWeights.radius*X)
        primeDetectorCutoff (X^ξ) u*
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (r*u)

theorem distinguishedLargeArityLow_remainder_arity {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ k : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (ℓ : ℤ) (Ct : ℕ) (H : ℝ),
      distinguishedLargeArityLow i ℓ ξ Ct H X =
        ∑ j ∈ Finset.range k, distinguishedDoubleArityLow i j ℓ ξ Ct H X := by
  obtain ⟨k,hbound⟩ := rough_slice_by_arity hξ
    (Real.exp_pos primeProductWeights.radius)
    (fun _ _ hx => primeDetectorCutoff_one hx)
  refine ⟨k,?_⟩
  filter_upwards [hbound] with X hX
  intro i ℓ Ct H
  unfold distinguishedLargeArityLow distinguishedDoubleArityLow
  simp_rw [hX (centralProductEnvelope X) _ _ (fun _ hn => centralProductEnvelope_spec hn),
    Finset.mul_sum]
  rw [Finset.sum_comm]

theorem distinguishedLargeLow_double_arity {ξ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ k₁ k₂ : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (Ct : ℕ) (H : ℝ),
      distinguishedLargeLow ℓ ξ Ct H X =
        ∑ i ∈ Finset.range k₁, ∑ j ∈ Finset.range k₂,
          distinguishedDoubleArityLow i j ℓ ξ Ct H X := by
  obtain ⟨k₁,h₁⟩ := distinguishedLargeLow_by_arity hξ hξz
  obtain ⟨k₂,h₂⟩ := distinguishedLargeArityLow_remainder_arity hξ
  refine ⟨k₁,k₂,?_⟩
  filter_upwards [h₁,h₂] with X h₁ h₂
  intro ℓ Ct H
  rw [h₁ ℓ Ct H]
  apply Finset.sum_congr rfl
  intro i _hi
  exact h₂ i ℓ Ct H

end CubicFirstMoment

end

end OAI
