import OAI.Probability.InvariantIsing.Spectral.SpectralEnergyPrimitive

namespace OAI

/-! The temperature-scaled group diagonals and the interaction energy. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteR_scale_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    finiteR ρ (fun a => t * eig a) hρ hρsum x =
      t * finiteR ρ eig hρ hρsum (t * x) := by
  rcases ht.eq_or_lt with h | h
  · subst t
    simp only [zero_mul, finiteR_constant]
  · exact finiteR_scale ρ eig hρ hρsum hx h

theorem projectedResolventDerivative_scale (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    projectedResolventDerivative ρ (fun b => t * eig b) hρ hρsum a x =
      projectedResolventDerivative ρ eig hρ hρsum a (t * x) := by
  rw [projectedResolventDerivative_eq_regular ρ (fun b => t * eig b) hρ hρsum a hx,
    projectedResolventDerivative_eq_regular ρ eig hρ hρsum a (mul_nonneg ht hx),
    finiteR_scale_nonneg ρ eig hρ hρsum hx ht]
  have he : ∀ b, 1 + x * (t * finiteR ρ eig hρ hρsum (t * x) - t * eig b) =
      1 + (t * x) * (finiteR ρ eig hρ hρsum (t * x) - eig b) := by intro b; ring
  simp_rw [he]

/-- The derivative formula for energy is exactly the weighted group-diagonal
formula for the spectrum at temperature `t`, including zero temperature. -/
theorem finiteInteractionEnergy_eq_groupDiagonal (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t : ℝ} (ht : 0 ≤ t) (p : OverlapPath) :
    finiteInteractionEnergy ρ eig hρ hρsum t p =
      (1 / 2 : ℝ) * ∑ a, eig a *
        spectralGroupDiagonal ρ (fun b => t * eig b) hρ hρsum p a := by
  unfold finiteInteractionEnergy spectralFunctional spectralGroupDiagonal
  congr 1
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum (fun a _ =>
    (spectralPathDensity_intervalIntegrable ρ (fun b => t * eig b) hρ hρsum p a
      ⟨zero_le_one, le_rfl⟩).const_mul (eig a))]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  change (∫ r, finiteSpectralSlope ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure) =
    ∫ r, (∑ a, eig a * spectralPathDensity ρ (fun b => t * eig b) hρ hρsum p a r)
      ∂pathMeasure
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  unfold finiteSpectralSlope spectralPathDensity
  apply Finset.sum_congr rfl
  intro a _
  rw [projectedResolventDerivative_scale ρ eig hρ hρsum a (deficit_nonneg p hr.2.le) ht]

end InvariantIsing

end

end OAI
