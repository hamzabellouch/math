import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowLaplaceRepresentation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! # The Euler integral on the positive spatial ray -/

open MeasureTheory

namespace DefocusingNLS

noncomputable def slowEulerKernel (q : ℂ) (m : ℕ) (x : ℂ) (v : ℝ) : ℂ :=
  Complex.exp (-x * (v : ℂ)) * (v : ℂ) ^ (q - 1) *
    (1 + (v : ℂ)) ^ ((m : ℂ) - 1 - q)

theorem slowLaplaceKernel_rescale (q : ℂ) (m : ℕ) {x v : ℝ}
    (hx : 0 < x) (hv : 0 ≤ v) :
    slowLaplaceKernel q m (x : ℂ) (x * v) =
      (x : ℂ) ^ (q - 1) * slowEulerKernel q m x v := by
  have hdiv : ((x : ℂ) * (v : ℂ)) / (x : ℂ) = (v : ℂ) := by
    exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hx.ne')
  simp only [slowLaplaceKernel, slowEulerKernel, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hx.le hv, hdiv, neg_mul]
  ring

theorem integrable_slowEulerKernel_real (q : ℂ) (m : ℕ) {x : ℝ}
    (hq : 0 < q.re) (hx : 0 < x) :
    IntegrableOn (slowEulerKernel q m (x : ℂ)) (Set.Ioi 0) := by
  have hi := integrable_slowLaplaceKernel q m (x : ℂ) hq
    (by simpa using hx.le) (Complex.ofReal_ne_zero.mpr hx.ne')
  have hs : IntegrableOn (fun v : ℝ => slowLaplaceKernel q m (x : ℂ) (x * v))
      (Set.Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff _ 0 hx).mpr
    simpa only [mul_zero] using hi
  have hp : (x : ℂ) ^ (q - 1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  apply (hs.const_mul ((x : ℂ) ^ (q - 1))⁻¹).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [slowLaplaceKernel_rescale q m hx (le_of_lt hv), ← mul_assoc, inv_mul_cancel₀ hp,
    one_mul]

/-- The substitution used in the manuscript before differentiation and
integration by parts. -/
theorem regularizedSlowSolution_eq_euler (q : ℂ) (m : ℕ) {x : ℝ}
    (hq : 0 < q.re) (hx : 0 < x) :
    regularizedSlowSolution q m (x : ℂ) = (Complex.Gamma q)⁻¹ *
      ∫ v : ℝ in Set.Ioi 0, slowEulerKernel q m (x : ℂ) v := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hsub := integral_comp_mul_left_Ioi' (slowLaplaceKernel q m (x : ℂ)) 0 hx
  simp only [mul_zero, Complex.real_smul] at hsub
  have he : (∫ v : ℝ in Set.Ioi 0, slowLaplaceKernel q m (x : ℂ) (x * v)) =
      (x : ℂ) ^ (q - 1) * ∫ v : ℝ in Set.Ioi 0, slowEulerKernel q m (x : ℂ) v := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    exact slowLaplaceKernel_rescale q m hx (le_of_lt hv)
  rw [he] at hsub
  have hp : (x : ℂ) * (x : ℂ) ^ (q - 1) = (x : ℂ) ^ q := by
    calc
      (x : ℂ) * (x : ℂ) ^ (q - 1) = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (q - 1) := by
        rw [Complex.cpow_one]
      _ = (x : ℂ) ^ (1 + (q - 1)) := (Complex.cpow_add _ _ hx0).symm
      _ = (x : ℂ) ^ q := by congr 1; ring
  have hc : (x : ℂ) ^ (-q) * (x : ℂ) ^ q = 1 := by
    rw [← Complex.cpow_add _ _ hx0, neg_add_cancel, Complex.cpow_zero]
  rw [regularizedSlowSolution_eq_laplace q m x hq (by simpa using hx.le) hx0, ← hsub]
  calc
    _ = ((x : ℂ) ^ (-q) * ((x : ℂ) * (x : ℂ) ^ (q - 1))) *
        ((Complex.Gamma q)⁻¹ * ∫ v : ℝ in Set.Ioi 0, slowEulerKernel q m (x : ℂ) v) := by ring
    _ = _ := by rw [hp, hc, one_mul]

end DefocusingNLS

end OAI
