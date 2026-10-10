import OAI.NumberTheory.JointDickman.Counting.CountingSiteModel
import OAI.NumberTheory.JointDickman.Counting.LagEnvelopeMoments

namespace OAI

/-! # Explicit row moments for the symmetric counting-feature model -/
namespace JointDickman
open Finset PublishedInputs

theorem countingSiteModel_row_moments
    (hMP : PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {η C₀ σ : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hC₀ : 0 ≤ C₀) (hH : η*T ≤ H)
    (hbound : ∀ j : ℕ, H < j → j < T →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀) :
    (∀ (i : Fin M) (a : (auxiliaryPrimes B).powerset),
      |siteRowMean (fun _ : Fin M => independentPrimeSetMass B)
        (countingSiteModel P m B L T H M τ C c D σ) i a| ≤
        2*(independentRootMean B L τ C*C₀/η)*Real.exp 24) ∧
    (∀ i : Fin M, siteRowSquareMass (fun _ : Fin M => independentPrimeSetMass B)
        (countingSiteModel P m B L T H M τ C c D σ) i ≤
        2*(independentRootMean B L τ C*C₀/η)^2*Real.exp 1200/(T : ℝ)) := by
  let A := independentRootMean B L τ C*C₀/η
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (independentRootMean_nonneg ..) hC₀) hη.le
  have he (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
      |countingSiteModel P m B L T H M τ C c D σ i k a b| ≤ lagEnvelope T A i k := by
    apply (countingSiteModel_lag_envelope hMP P m B L T H M τ C c D hT hη hC₀ hH hbound i k a b).trans_eq
    unfold lagEnvelope A
    split_ifs <;> ring
  exact ⟨fun i a => lagEnvelope_row_mean hT hA _
    (fun _ => independentPrimeSetMass_nonneg B) (fun _ => independentPrimeSetMass_sum B)
    _ he i a,
    fun i => lagEnvelope_row_square_mass hT hA _
      (fun _ => independentPrimeSetMass_nonneg B) (fun _ => independentPrimeSetMass_sum B)
      _ he i⟩

end JointDickman

end OAI
