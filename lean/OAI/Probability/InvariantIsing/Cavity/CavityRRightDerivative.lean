import OAI.Probability.InvariantIsing.Cavity.CavityRDerivative

namespace OAI

/-! The one-sided derivative at zero follows from the continuous density
primitive. The constant negative-argument extension is not differentiated. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem hasDerivWithinAt_cavityR_nonneg (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (finiteR rho lam hrho hsum)
      (cavityRDerivative rho lam hrho hsum x) (Ici 0) x := by
  have hc := continuous_cavityRDerivative rho lam hrho hsum
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (μ := volume) 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd := (hi.const_add (finiteR rho lam hrho hsum 0)).hasDerivWithinAt (s := Ici 0)
  apply hd.congr_of_mem _ hx
  intro y hy
  have he := integral_cavityRDerivative rho lam hrho hsum (a := 0) (b := y) le_rfl hy
  linarith

theorem hasDerivWithinAt_cavityR_zero (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) :
    HasDerivWithinAt (finiteR rho lam hrho hsum)
      (∑ a, rho a * (lam a - ∑ b, rho b * lam b) ^ 2) (Ici 0) 0 := by
  simpa only [cavityRDerivative_zero] using
    hasDerivWithinAt_cavityR_nonneg rho lam hrho hsum (x := 0) le_rfl

end InvariantIsing

end

end OAI
