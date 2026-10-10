import OAI.Geometry.EinsteinFour.SineAverage
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

namespace OAI

/-! The first-mode averaging estimate in the actual space of square-integrable
fields. Stationarity is an integral over the space of initial geodesics; no
pointwise constancy along a geodesic is assumed. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

omit [CompleteSpace E] in
/-- The Hilbert norm used for geodesic averaging is exactly the mean square
of the continuous field, with respect to the chosen finite measure. -/
theorem continuous_toL2_norm_sq (f : C(Ω, E)) :
    ‖ContinuousMap.toLp 2 μ ℝ f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    (∫ x, inner ℝ ((ContinuousMap.toLp 2 μ ℝ f) x)
      ((ContinuousMap.toLp 2 μ ℝ f) x) ∂μ) = ∫ x, inner ℝ (f x) (f x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f] with x hx
        rw [hx]
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

/-- Averaging a field first in time and then in space gives the same squared
norm as the Bochner average in the actual `L²` space. -/
theorem continuous_toL2_average_norm_sq {F : ℝ → C(Ω, E)}
    (hF : Integrable F sineMeasure) :
    ‖∫ u, ContinuousMap.toLp 2 μ ℝ (F u) ∂sineMeasure‖ ^ 2 =
      ∫ x, ‖∫ u, F u x ∂sineMeasure‖ ^ 2 ∂μ := by
  rw [(ContinuousMap.toLp 2 μ ℝ).integral_comp_comm hF,
    continuous_toL2_norm_sq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [ContinuousMap.integral_apply hF x]

/-- The geodesic first-mode bound, obtained from stationarity of mean-square
curvature and its mean-square derivative bound. The hypotheses are ordinary
field identities and derivatives; the conclusion is the iterated integral
needed in the radial determinant comparison. -/
theorem geodesic_mean_square_lower {F G : ℝ → C(Ω, E)} {q t : ℝ}
    (hq : 0 ≤ q)
    (hderiv : ∀ r, HasDerivAt F (G r) r)
    (hstationary : ∀ r, (∫ x, ‖F r x‖ ^ 2 ∂μ) = q)
    (henergy : ∀ r, (∫ x, ‖G r x‖ ^ 2 ∂μ) ≤ (3 / 2) * q) :
    q * (1 - (t / Real.pi) ^ 2 / 2) ≤
      ∫ x, ‖∫ u, F (t * u) x ∂sineMeasure‖ ^ 2 ∂μ := by
  let T : C(Ω, E) →L[ℝ] Lp E 2 μ := ContinuousMap.toLp 2 μ ℝ
  have hd (u : ℝ) : HasDerivAt (fun u => T (F (t * u))) (t • T (G (t * u))) u := by
    exact ((T.hasFDerivAt.comp_hasDerivAt (t * u) (hderiv (t * u))).scomp u
      (by simpa using (hasDerivAt_id u).const_mul t))
  have hs : ∀ᵐ u ∂sineMeasure, ‖T (F (t * u))‖ ^ 2 = q :=
    Filter.Eventually.of_forall fun u => (continuous_toL2_norm_sq _).trans (hstationary _)
  have hb (u : ℝ) : ‖t • T (G (t * u))‖ ^ 2 ≤
      (3 / 2) * q * (Real.pi * (t / Real.pi)) ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, continuous_toL2_norm_sq]
    have he := mul_le_mul_of_nonneg_left (henergy (t * u)) (sq_nonneg t)
    field_simp [Real.pi_ne_zero]
    nlinarith only [he]
  have h := sine_average_lower_of_derivative hq hd hs hb
  have hc : Continuous (fun u => F (t * u)) :=
    (continuous_iff_continuousAt.mpr fun r => (hderiv r).continuousAt).comp
      (continuous_const.mul continuous_id)
  rwa [continuous_toL2_average_norm_sq (integrable_sineMeasure hc)] at h

end

end PositiveEinsteinFour.Averages

end OAI
