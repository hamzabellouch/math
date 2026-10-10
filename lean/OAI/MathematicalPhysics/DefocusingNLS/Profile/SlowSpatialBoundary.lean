import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowSlitDomination

namespace OAI

/-! # Spatial holomorphy across the nonzero imaginary boundary -/

open MeasureTheory Filter Topology

namespace DefocusingNLS

theorem hasDerivAt_integral_regularizedSlowKernel_of_im_ne_zero
    (q : ℂ) (m : ℕ) (x : ℂ) (hq : -1 < q.re) (hx : x.im ≠ 0) :
    HasDerivAt (fun z : ℂ => ∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel q m z u)
      (∫ u : ℝ in Set.Ioi 0, slowKernelSpatialDerivative q m x u) x := by
  let c : ℝ := |x.im| / 2
  let M : ℝ := ‖x‖ + 1
  have hc : 0 < c := half_pos (abs_pos.mpr hx)
  have hM : 0 < M := by dsimp [M]; positivity
  let s : Set ℂ := {z | c < |z.im| ∧ ‖z‖ < M}
  have hs : s ∈ 𝓝 x := by
    apply ((isOpen_lt continuous_const Complex.continuous_im.abs).inter
      (isOpen_lt continuous_norm continuous_const)).mem_nhds
    constructor
    · dsimp [c]
      linarith [abs_pos.mpr hx]
    · dsimp [M]
      linarith
  have hslit (z : ℂ) (hz : z ∈ s) : z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    exact abs_pos.mp (hc.trans hz.1)
  have hxslit : x ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr hx)
  obtain ⟨bound, hbound, hle⟩ :=
    exists_slowKernelSpatialDerivative_majorant_of_im q m hq c M hc hM
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun z u => regularizedSlowKernel q m z u)
    (F' := fun z u => slowKernelSpatialDerivative q m z u)
    (bound := bound) hs
    (Eventually.of_forall fun z => (measurable_regularizedSlowKernel q m z).aestronglyMeasurable.restrict)
    (integrable_regularizedSlowKernel_of_slit q m x hq hxslit)
    (integrable_slowKernelSpatialDerivative_of_slit q m x hq hxslit).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro z hz
      exact hle z hz.1.le hz.2.le u hu)
    hbound
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro z hz
      exact hasDerivAt_regularizedSlowKernel_spatial_of_slit q m z (hslit z hz) hu.le)).2

theorem differentiableAt_regularizedSlowSolution_of_im_ne_zero
    (q : ℂ) (m : ℕ) (x : ℂ) (hq : -1 < q.re) (hx : x.im ≠ 0) :
    DifferentiableAt ℂ (regularizedSlowSolution q m) x := by
  have hp := (hasDerivAt_id x).cpow_const (c := -q)
    (Complex.mem_slitPlane_iff.mpr (Or.inr hx))
  have hi := ((hasDerivAt_integral_regularizedSlowKernel_of_im_ne_zero q m x hq hx).const_mul
    (Complex.Gamma q)⁻¹).const_add 1
  convert! (hp.fun_mul hi).differentiableAt using 1

/-- The original integral, on its natural slit domain, supplies the
holomorphic continuation across every nonzero imaginary point. -/
theorem differentiableOn_regularizedSlowSolution_slit (q : ℂ) (m : ℕ)
    (hq : -1 < q.re) :
    DifferentiableOn ℂ (regularizedSlowSolution q m) Complex.slitPlane := by
  intro x hx
  rcases Complex.mem_slitPlane_iff.mp hx with hre | him
  · exact (hasDerivAt_regularizedSlowSolution q m x hq hre).differentiableAt.differentiableWithinAt
  · exact (differentiableAt_regularizedSlowSolution_of_im_ne_zero q m x hq him).differentiableWithinAt

theorem analyticOnNhd_regularizedSlowSolution_slit (q : ℂ) (m : ℕ)
    (hq : -1 < q.re) :
    AnalyticOnNhd ℂ (regularizedSlowSolution q m) Complex.slitPlane :=
  (differentiableOn_regularizedSlowSolution_slit q m hq).analyticOnNhd Complex.isOpen_slitPlane

end DefocusingNLS

end OAI
