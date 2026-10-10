import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowInitialEquation

namespace OAI

/-! # Integration by parts across the first regularized parameter strip

The primitive retains the subtraction at zero. Its boundary term vanishes
for `Re(q) > -1`, which relates the regularized integral to ordinary
Laplace integrals at `q+1`.
-/

open MeasureTheory Filter Topology Asymptotics

namespace DefocusingNLS

noncomputable def slowRegularizedPrimitive (q : ℂ) (m : ℕ) (x : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-(u : ℂ)) * (u : ℂ) ^ q *
    regularizingBracket ((m : ℂ) - 1 - q) x u

noncomputable def slowRegularizedBoundaryDerivative (q : ℂ) (m : ℕ)
    (x : ℂ) (u : ℝ) : ℂ :=
  q * regularizedSlowKernel q m x u - regularizedSlowKernel (q + 1) (m + 1) x u +
    (((m : ℂ) - 1 - q) / x) * slowLaplaceKernel (q + 1) m x u

theorem slowRegularizedPrimitive_eq_kernel (q : ℂ) (m : ℕ) (x : ℂ) :
    slowRegularizedPrimitive q m x = regularizedSlowKernel (q + 1) (m + 1) x := by
  funext u
  have he : ((m + 1 : ℕ) : ℂ) - 1 - (q + 1) = (m : ℂ) - 1 - q := by
    push_cast
    ring
  simp only [slowRegularizedPrimitive, regularizedSlowKernel, add_sub_cancel_right, he]

theorem hasDerivAt_slowRegularizedPrimitive (q : ℂ) (m : ℕ) (x : ℂ)
    (hx : 0 ≤ x.re) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (slowRegularizedPrimitive q m x)
      (slowRegularizedBoundaryDerivative q m x u) u := by
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have he := ((hasDerivAt_id (u : ℂ)).neg.cexp)
  have hp := (hasDerivAt_id (u : ℂ)).cpow_const (c := q)
    (Complex.ofReal_mem_slitPlane.mpr hu)
  have hb := ((((hasDerivAt_id (u : ℂ)).div_const x).const_add 1).cpow_const
    (c := (m : ℂ) - 1 - q) (one_add_real_div_mem_slitPlane x hx hu.le)).sub_const 1
  have hh := ((he.fun_mul hp).fun_mul hb).comp_ofReal
  have hp' : (u : ℂ) ^ q = (u : ℂ) ^ (q - 1) * (u : ℂ) := by
    calc
      _ = (u : ℂ) ^ (q - 1 + 1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
  have he₁ : ((m + 1 : ℕ) : ℂ) - 1 - (q + 1) = (m : ℂ) - 1 - q := by
    push_cast
    ring
  have he₂ : (m : ℂ) - 1 - (q + 1) = (m : ℂ) - 1 - q - 1 := by ring
  convert! hh using 1
  simp only [slowRegularizedBoundaryDerivative, regularizedSlowKernel,
    slowLaplaceKernel, regularizingBracket, he₁, he₂, add_sub_cancel_right,
    id_eq, mul_one, Pi.neg_apply, one_div]
  rw [hp']
  ring

theorem integrable_slowRegularizedBoundaryDerivative (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    IntegrableOn (slowRegularizedBoundaryDerivative q m x) (Set.Ioi 0) := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  exact (((integrable_regularizedSlowKernel q m x hq hx hx0).const_mul q).sub
    (integrable_regularizedSlowKernel (q + 1) (m + 1) x (by linarith) hx hx0)).add
      ((integrable_slowLaplaceKernel (q + 1) m x hq' hx hx0).const_mul
        (((m : ℂ) - 1 - q) / x))

theorem slowRegularizedPrimitive_tendsto_zero (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) :
    Tendsto (slowRegularizedPrimitive q m x) (𝓝[>] 0) (𝓝 0) := by
  rw [slowRegularizedPrimitive_eq_kernel]
  apply (regularizedSlowKernel_isBigO_zero (q + 1) (m + 1) x).trans_tendsto
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  have h : Tendsto (fun u : ℝ => u ^ (q + 1).re) (𝓝[>] 0) (𝓝 (0 ^ (q + 1).re)) :=
    (Real.continuousAt_rpow_const (0 : ℝ) (q + 1).re
      (Or.inr hq'.le)).tendsto.mono_left nhdsWithin_le_nhds
  simpa only [Real.zero_rpow hq'.ne'] using h

theorem integral_slowRegularizedBoundaryDerivative (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    (∫ u : ℝ in Set.Ioi 0, slowRegularizedBoundaryDerivative q m x u) = 0 := by
  have hi := integrable_slowRegularizedBoundaryDerivative q m x hq hx hx0
  have hp : IntegrableOn (slowRegularizedPrimitive q m x) (Set.Ioi 0) := by
    rw [slowRegularizedPrimitive_eq_kernel]
    apply integrable_regularizedSlowKernel _ _ _ _ hx hx0
    change -1 < q.re + 1
    linarith
  have hd := fun u (hu : u ∈ Set.Ioi (0 : ℝ)) =>
    hasDerivAt_slowRegularizedPrimitive q m x hx hu
  have hlim := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hd hi hp
  have hz : slowRegularizedPrimitive q m x 0 = 0 := by
    simp [slowRegularizedPrimitive, regularizingBracket]
  have hc : ContinuousWithinAt (slowRegularizedPrimitive q m x) (Set.Ici 0) 0 := by
    rw [ContinuousWithinAt, hz, ← Set.Ioi_union_left, nhdsWithin_union]
    exact (slowRegularizedPrimitive_tendsto_zero q m x hq).sup
      (by simpa only [nhdsWithin_singleton, hz] using
        tendsto_pure_nhds (slowRegularizedPrimitive q m x) (0 : ℝ))
  simpa only [hz, sub_zero] using integral_Ioi_of_hasDerivAt_of_tendsto hc hd hi hlim

theorem slowRegularized_integral_recurrence (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    q * (∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel q m x u) =
      (∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel (q + 1) (m + 1) x u) -
        (((m : ℂ) - 1 - q) / x) *
          (∫ u : ℝ in Set.Ioi 0, slowLaplaceKernel (q + 1) m x u) := by
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  have h₀ := integrable_regularizedSlowKernel q m x hq hx hx0
  have h₁ := integrable_regularizedSlowKernel (q + 1) (m + 1) x (by linarith) hx hx0
  have h₂ := integrable_slowLaplaceKernel (q + 1) m x hq' hx hx0
  have h := integral_slowRegularizedBoundaryDerivative q m x hq hx hx0
  unfold slowRegularizedBoundaryDerivative at h
  rw [integral_add
    (f := fun u => q * regularizedSlowKernel q m x u -
      regularizedSlowKernel (q + 1) (m + 1) x u)
    (g := fun u => (((m : ℂ) - 1 - q) / x) * slowLaplaceKernel (q + 1) m x u)
    ((h₀.const_mul q).sub h₁) (h₂.const_mul (((m : ℂ) - 1 - q) / x)),
    integral_sub (h₀.const_mul q) h₁] at h
  simp only [integral_const_mul] at h
  linear_combination h

end DefocusingNLS

end OAI
