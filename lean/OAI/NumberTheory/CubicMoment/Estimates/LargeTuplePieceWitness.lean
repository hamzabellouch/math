import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleFullSupport

namespace OAI

/-! Nonzero actual pieces provide all coordinate-envelope hypotheses.
Thus no envelope admissibility is left as an extra analytic assumption. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largePrimeTuplePiece_witness {i j : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {Ct : ℕ} {H X : ℝ}
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hne : largePrimeTuplePiece i j ℓ ξ Ct H X k ≠ 0) :
    ∃ q ∈ largePrimeTupleBox i j X,
      largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  unfold largePrimeTuplePiece
  rw [Finset.sum_eq_zero h,mul_zero]

theorem eventually_largePrimeTuplePiece_high_full (i j : ℕ) {ξ : ℝ} (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (Ct : ℕ) (H : ℝ)
      (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val) →
      largePrimeTuplePiece i j ℓ ξ Ct H X k ≠ 0 →
      largePrimeTuplePiece i j ℓ ξ Ct H X k =
        ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
          largeTupleIndependentSum i j ℓ ξ Ct H X (fun a => (k a).val) := by
  filter_upwards [largePrimeTuplePiece_coordinate_envelope i j hξz,
    eventually_gt_atTop (0:ℝ)] with X hcoord hX
  intro ℓ Ct H k hhigh hne
  obtain ⟨q,hq,hqne⟩ := largePrimeTuplePiece_witness k hne
  exact largePrimeTuplePiece_high_full i j ℓ ξ Ct H hX k hhigh (hcoord ℓ Ct H k q hq hqne)

end CubicFirstMoment

end

end OAI
