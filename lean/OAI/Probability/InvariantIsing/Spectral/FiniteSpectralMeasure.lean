import OAI.Probability.InvariantIsing.Spectral.MeasureResolvent

namespace OAI

/-! The general measure transform agrees with the finite-alphabet transform.
Positive masses ensure that the upper edge is an atom and the inverse is uncapped. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def finiteSpectralMeasure (ρ eig : ι → ℝ) : Measure ℝ :=
  Measure.sum fun a => ENNReal.ofReal (ρ a) • Measure.dirac (eig a)

theorem finiteSpectralMeasure_probability (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (hsum : ∑ a, ρ a = 1) :
    IsProbabilityMeasure (finiteSpectralMeasure ρ eig) := by
  apply HasSum.isProbabilityMeasure_sum_dirac hρ
  simpa only [hsum] using hasSum_fintype ρ

theorem integral_finiteSpectralMeasure (ρ eig : ι → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (f : ℝ → ℝ) :
    (∫ y, f y ∂finiteSpectralMeasure ρ eig) = ∑ a, ρ a * f (eig a) := by
  have hi a : Integrable f (ENNReal.ofReal (ρ a) • Measure.dirac (eig a)) :=
    (integrable_dirac (by simp)).smul_measure (by finiteness)
  rw [finiteSpectralMeasure, Measure.sum_fintype,
    integral_finsetSum_measure (fun a _ => hi a)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hρ _), smul_eq_mul]

theorem ae_finiteSpectralMeasure (ρ eig : ι → ℝ) {P : ℝ → Prop} (hP : ∀ a, P (eig a)) :
    ∀ᵐ y ∂finiteSpectralMeasure ρ eig, P y := by
  rw [finiteSpectralMeasure, Measure.ae_sum_iff]
  intro a
  have hd : ∀ᵐ y ∂Measure.dirac (eig a), P y := by
    simpa only [ae_dirac_eq, Filter.eventually_pure] using hP a
  exact Measure.ae_smul_measure hd _

theorem measureResolvent_finiteSpectralMeasure (ρ eig : ι → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (b : ℝ) : measureResolvent (finiteSpectralMeasure ρ eig) b = finiteResolvent ρ eig b := by
  rw [measureResolvent, integral_finiteSpectralMeasure ρ eig hρ]
  simp only [finiteResolvent, mul_one_div]

theorem measureR_finiteSpectralMeasure (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (aMax : ι) (hMax : ∀ a, eig a ≤ eig aMax) (x : ℝ) :
    measureR (finiteSpectralMeasure ρ eig) (eig aMax) x = finiteR ρ eig hρ hsum x := by
  let := finiteSpectralMeasure_probability ρ eig (fun a => (hρ a).le) hsum
  by_cases hx : 0 < x
  · have hs := finiteInverse_spec ρ eig hρ hsum hx
    have hsol : measureResolvent (finiteSpectralMeasure ρ eig) (finiteInverse ρ eig hρ hsum x) = x := by
      rw [measureResolvent_finiteSpectralMeasure ρ eig (fun a => (hρ a).le)]
      exact hs.2
    have hi := measureInverse_eq_of_solution (finiteSpectralMeasure ρ eig)
      (ae_finiteSpectralMeasure ρ eig hMax) (hs.1 aMax) hsol
    simp only [measureR, finiteR, ite_eq_left hx, hi]
  · simp only [measureR, finiteR, ite_eq_right hx,
      integral_finiteSpectralMeasure ρ eig (fun a => (hρ a).le)]

end InvariantIsing

end

end OAI
