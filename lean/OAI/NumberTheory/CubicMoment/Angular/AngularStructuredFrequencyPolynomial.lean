import OAI.NumberTheory.CubicMoment.Angular.AngularFullPrimeConvolution
import OAI.NumberTheory.CubicMoment.Estimates.StructuredFrequencyPolynomial

namespace OAI

/-! Exact angular frequency coefficients; their energy is unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def structuredAngularFrequencyCoefficient (ℓ : ℤ) (v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) (z : Eisenstein) : ℂ :=
  theta ℓ z*structuredFrequencyCoefficient v e u W X Z z

lemma structuredAngularPrimeSum_eq_frequency (ℓ : ℤ) (h v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) :
    structuredAngularPrimeSum ℓ h 1 v e u W X Z =
      ∑ z ∈ structuredFrequencySupport W X Z,
        structuredAngularFrequencyCoefficient ℓ v e u W X Z z*cubicSymbol z h := by
  unfold structuredAngularPrimeSum structuredFrequencySupport
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have hp := orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
    (fun i p h => (coordinatePrimeSupport_primary W X Z i p h).1) hz
  by_cases hsf : Squarefree z
  · rw [ite_eq_left hsf]
    by_cases hc : IsCoprime z e
    · simp only [ite_eq_left hc,structuredAngularFrequencyCoefficient,
        structuredFrequencyCoefficient,one_pow,mul_one,cubicSymbol_mul_upper hp]
      ring
    · simp only [ite_eq_right hc,structuredAngularFrequencyCoefficient,
        structuredFrequencyCoefficient,mul_zero,zero_mul]
  · have he : primeMomentCoefficient W X Z z = 0 := by
      simp only [primeMomentCoefficient,squarefreeConvolution,ite_eq_right hsf]
    simp only [he,zero_mul,ite_eq_right hsf,ite_self]

lemma structuredAngularFrequencyCoefficient_energy_le (ℓ : ℤ) (v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) :
    (∑ z ∈ structuredFrequencySupport W X Z,
      ‖structuredAngularFrequencyCoefficient ℓ v e u W X Z z‖^2) ≤
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
        ‖primeMomentCoefficient W X Z z‖^2 := by
  have he : (∑ z ∈ structuredFrequencySupport W X Z,
      ‖structuredAngularFrequencyCoefficient ℓ v e u W X Z z‖^2) =
      ∑ z ∈ structuredFrequencySupport W X Z,
        ‖structuredFrequencyCoefficient v e u W X Z z‖^2 := by
    apply Finset.sum_congr rfl
    intro z hz
    have hp := orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
      (fun i p h => (coordinatePrimeSupport_primary W X Z i p h).1) (Finset.mem_filter.mp hz).1
    rw [structuredAngularFrequencyCoefficient,norm_mul,norm_theta (primary_ne_zero hp) ℓ,one_mul]
  rw [he]
  exact structuredFrequencyCoefficient_energy_le v e u W X Z

end CubicFirstMoment

end

end OAI
