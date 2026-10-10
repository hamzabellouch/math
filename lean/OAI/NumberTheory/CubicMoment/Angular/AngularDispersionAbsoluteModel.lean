import OAI.NumberTheory.CubicMoment.Estimates.DispersionAbsoluteModel
import OAI.NumberTheory.CubicMoment.Angular.AngularHeightCoefficient

namespace OAI
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
 theorem angular_logarithmic_dispersionAbsoluteModel_energy (ℓ : ℤ)
    {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (K : ℝ) (a : ℕ), 0 ≤ K ∧ ∀ r X e,
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      (dispersionAbsoluteModel (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X))^2 ≤
        K*(L r)^(5/3:ℝ)*(1+Real.log (L r))^a := by
  obtain ⟨K,a,hK,hb⟩ := logarithmic_dispersionAbsoluteModel_energy hW hR hlo hhi
  refine ⟨K,a,hK,?_⟩
  intro r X e hL hX hprod
  have he : dispersionAbsoluteModel (fullSquarefreePrimeSupport R (W r) X e)
      (angularHeightPrimeCoefficient ℓ R (W r) X) =
      dispersionAbsoluteModel (fullSquarefreePrimeSupport R (W r) X e)
      (fullPrimeCoefficient R (W r) X) := by
    unfold dispersionAbsoluteModel
    apply Finset.sum_congr rfl
    intro b hb
    rw [angularHeightPrimeCoefficient_norm ℓ R (W r) X
      (fullSquarefreePrimeSupport_primary R (W r) X e hb).1]
  rw [he]
  exact hb r X e hL hX hprod
end CubicFirstMoment

end

end OAI
