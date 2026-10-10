import OAI.NumberTheory.CubicMoment.Estimates.GramStructuredRows
import OAI.NumberTheory.CubicMoment.Estimates.StructuredHeightMass

namespace OAI

/-! The empty common-divisor term consists exactly of the two signed
full height masses; the prime coefficients are unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrime_empty_divisor_mass (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (H : Finset Eisenstein) (e : Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    ((∑ h ∈ H, ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter
        (fun a => (∏ p ∈ (∅ : Finset Eisenstein), p) ∣ a),
      star (fullPrimeCoefficient R W X a*mellinPhase u (norm a))*
        star (gramMellinPhase t (norm a/N))*star (cubicSymbol a h)‖^2)+
    (∑ h ∈ H, ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter
        (fun a => (∏ p ∈ (∅ : Finset Eisenstein), p) ∣ a),
      star (fullPrimeCoefficient R W X a*mellinPhase u (norm a))*
        gramMellinPhase t (norm a/N)*star (cubicSymbol a h)‖^2))/2 =
    (fullStructuredHeightMass R H 1 e 0 u W X (2*Real.pi*t)+
      fullStructuredHeightMass R H 1 e 0 u W X (-(2*Real.pi*t)))/2 := by
  simp only [Finset.prod_empty,one_dvd,Finset.filter_true,fullStructuredHeightMass,
    fullStructuredAngularSum_zero,fullStructuredPrimeRow_norm R W X _ e u t hN,
    fullStructuredPrimeRow_reverse_norm R W X _ e u t hN,add_comm (2*Real.pi*t) u,
    sub_eq_add_neg,add_comm (-(2*Real.pi*t)) u]

end CubicFirstMoment

end

end OAI
