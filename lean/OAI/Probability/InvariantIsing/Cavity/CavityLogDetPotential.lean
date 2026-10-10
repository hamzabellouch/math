import OAI.Probability.InvariantIsing.Cavity.CavityRRightDerivative
import OAI.Probability.InvariantIsing.Cavity.CavitySchurDerivative

namespace OAI

/-! A continuous zero-endpoint form of the scalar logarithmic determinant.
It retains the ordinary residual contribution, whose cascade exponent is one. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def cavityLogDetPotential {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (x : ℝ) : ℝ :=
  ∑ a, rho a * Real.log (1 + x * (finiteR rho lam hrho hsum x - lam a))

lemma cavityLogDetPotential_argument_pos {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {x : ℝ} (hx : 0 ≤ x) (a : Fin m) :
    0 < 1 + x * (finiteR rho lam hrho hsum x - lam a) := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num
  · have he : 1 + x * (finiteR rho lam hrho hsum x - lam a) =
        x * (finiteInverse rho lam hrho hsum x - lam a) := by
      simp only [finiteR, ite_eq_left hx]
      field_simp [hx.ne']
      ring
    rw [he]
    exact mul_pos hx (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hx).1 a))

lemma cavityLogDetPotential_zero {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) :
    cavityLogDetPotential rho lam hrho hsum 0 = 0 := by
  simp [cavityLogDetPotential]

lemma continuousOn_cavityLogDetPotential {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) :
    ContinuousOn (cavityLogDetPotential rho lam hrho hsum) (Ici 0) := by
  apply continuousOn_finsetSum
  intro a _
  apply continuousOn_const.mul
  exact (continuous_const.add (continuous_id.mul
    ((continuous_finiteR rho lam hrho hsum).sub continuous_const))).continuousOn.log
      (fun x hx => (cavityLogDetPotential_argument_pos rho lam hrho hsum hx a).ne')

lemma cavityLogDetPotential_eq {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {x : ℝ} (hx : 0 < x) :
    cavityLogDetPotential rho lam hrho hsum x = cavitySpectralLogDet rho lam hrho hsum x := by
  have he (a : Fin m) : 1 + x * (finiteR rho lam hrho hsum x - lam a) =
      x * (finiteInverse rho lam hrho hsum x - lam a) := by
    simp only [finiteR, ite_eq_left hx]
    field_simp [hx.ne']
    ring
  have hl (a : Fin m) : Real.log (1 + x * (finiteR rho lam hrho hsum x - lam a)) =
      Real.log x + Real.log (finiteInverse rho lam hrho hsum x - lam a) := by
    rw [he a, Real.log_mul hx.ne'
      (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hx).1 a)).ne']
  unfold cavityLogDetPotential cavitySpectralLogDet
  simp_rw [hl, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]

lemma hasDerivAt_cavityLogDetPotential {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (cavityLogDetPotential rho lam hrho hsum)
      (x * cavityRDerivative rho lam hrho hsum x) x := by
  have he : cavityLogDetPotential rho lam hrho hsum =ᶠ[𝓝 x]
      cavitySpectralLogDet rho lam hrho hsum := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact cavityLogDetPotential_eq rho lam hrho hsum hy
  rw [cavityRDerivative_eq_deriv rho lam hrho hsum hx]
  exact (hasDerivAt_cavitySpectralLogDet rho lam hrho hsum x hx).congr_of_eventuallyEq he

theorem integral_cavityLogDetPotential_derivative {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, x * cavityRDerivative rho lam hrho hsum x) =
      cavityLogDetPotential rho lam hrho hsum b - cavityLogDetPotential rho lam hrho hsum a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    ((continuousOn_cavityLogDetPotential rho lam hrho hsum).mono
      (fun _ hx => ha.trans hx.1))
  · intro x hx
    exact hasDerivAt_cavityLogDetPotential rho lam hrho hsum (ha.trans_lt hx.1)
  · exact (continuous_id.mul (continuous_cavityRDerivative rho lam hrho hsum)).intervalIntegrable a b

end InvariantIsing

end

end OAI
