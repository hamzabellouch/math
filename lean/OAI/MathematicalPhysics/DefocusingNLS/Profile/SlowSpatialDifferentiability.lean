import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowKernelDomination
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! # Spatial differentiability of the regularized definition -/

open MeasureTheory Filter Topology

namespace DefocusingNLS

theorem hasDerivAt_integral_regularizedSlowKernel (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 < x.re) :
    HasDerivAt (fun z : ℂ => ∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel q m z u)
      (∫ u : ℝ in Set.Ioi 0, slowKernelSpatialDerivative q m x u) x := by
  let c : ℝ := x.re / 2
  have hc : 0 < c := half_pos hx
  obtain ⟨bound, hbound, hle⟩ := exists_slowKernelSpatialDerivative_majorant q m hq c hc
  let s : Set ℂ := {z | c < z.re}
  have hs : s ∈ 𝓝 x := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by dsimp [s, c]; linarith)
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun z u => regularizedSlowKernel q m z u)
    (F' := fun z u => slowKernelSpatialDerivative q m z u)
    (bound := bound) hs
    (Eventually.of_forall fun z => (measurable_regularizedSlowKernel q m z).aestronglyMeasurable.restrict)
    (integrable_regularizedSlowKernel q m x hq hx.le hx0)
    (integrable_slowKernelSpatialDerivative q m x hq hx.le hx0).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro z hz
      exact hle z (le_of_lt hz) u hu)
    hbound
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro z hz
      have hzpos : 0 < z.re := hc.trans hz
      have hz0 : z ≠ 0 := by intro h; simp [h] at hzpos
      exact hasDerivAt_regularizedSlowKernel_spatial q m z hzpos.le hz0 (le_of_lt hu))
  exact h.2

theorem hasDerivAt_regularizedSlowSolution (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 < x.re) :
    HasDerivAt (regularizedSlowSolution q m)
      ((-q) * x ^ (-q - 1) *
          (1 + (Complex.Gamma q)⁻¹ * ∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel q m x u) +
        x ^ (-q) * ((Complex.Gamma q)⁻¹ *
          ∫ u : ℝ in Set.Ioi 0, slowKernelSpatialDerivative q m x u)) x := by
  have hp := (hasDerivAt_id x).cpow_const (c := -q)
    (Complex.mem_slitPlane_iff.mpr (Or.inl hx))
  have hi := ((hasDerivAt_integral_regularizedSlowKernel q m x hq hx).const_mul
    (Complex.Gamma q)⁻¹).const_add 1
  convert! hp.fun_mul hi using 1
  all_goals simp only [mul_one, id_eq]

theorem differentiableOn_regularizedSlowSolution (q : ℂ) (m : ℕ) (hq : -1 < q.re) :
    DifferentiableOn ℂ (regularizedSlowSolution q m) {x : ℂ | 0 < x.re} := by
  intro x hx
  exact (hasDerivAt_regularizedSlowSolution q m x hq hx).differentiableAt.differentiableWithinAt

end DefocusingNLS

end OAI
