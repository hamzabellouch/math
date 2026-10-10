import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialIdentification
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFastTail

namespace OAI

/-! # Smooth radial channels of homogeneous-space vectors

Exterior ODE regularity supplies smoothness. The completed Fourier norm then
forces the classical top radial derivative to lie in L²(r¹¹dr), excluding
the nonintegrable fast asymptotic coefficient.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

theorem hasDerivAt_iteratedDeriv_on_open (U : Set ℝ) (hU : IsOpen U)
    (f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f U) (j : ℕ) (r : ℝ) (hr : r ∈ U) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f r) r := by
  have hd := hf.differentiableOn_iteratedDerivWithin (m := j)
    (by exact_mod_cast ENat.natCast_lt_top j) hU.uniqueDiffOn
  have he : DifferentiableOn ℝ (iteratedDeriv j f) U := hd.congr
    (fun x hx => (iteratedDerivWithin_of_isOpen hU hx).symm)
  simpa only [iteratedDeriv_succ] using
    ((he r hr).differentiableAt (hU.mem_nhds hr)).hasDerivAt

/-- Smoothness only on the exterior suffices for the exact weighted L² bound. -/
theorem homogeneousAngularProjection_iteratedDeriv_integrable
    (a : ℝ) (N : ℕ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (h : PhysicalUnitSphere → ℂ) (hh : MemLp h 2 physicalSphereMeasure)
    (u : HomogeneousY a N) (R : ℝ) (hR : 0 ≤ R)
    (hsmooth : ContDiffOn ℝ ∞ (homogeneousAngularProjection a N ha ha1 hk h u) (Ioi R)) :
    IntegrableOn (fun r : ℝ => r ^ (11 : ℕ) *
      ‖iteratedDeriv N (homogeneousAngularProjection a N ha ha1 hk h u) r‖ ^ 2) (Ioi R) := by
  apply homogeneousRadial_classical_weighted_square a N ha ha1 hk h hh u R hR
    (fun j => iteratedDeriv j (homogeneousAngularProjection a N ha ha1 hk h u))
  · intro j r hr
    exact hasDerivAt_iteratedDeriv_on_open (Ioi R) isOpen_Ioi _ hsmooth j r hr
  · funext r
    rfl

/-- A fast-mode asymptotic at or above the radial L² threshold must have
zero coefficient for a genuine homogeneous-space vector. -/
theorem homogeneousAngularProjection_fast_coefficient_zero
    (a : ℝ) (N : ℕ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (h : PhysicalUnitSphere → ℂ) (hh : MemLp h 2 physicalSphereMeasure)
    (u : HomogeneousY a N) (R : ℝ) (hR : 0 ≤ R)
    (hsmooth : ContDiffOn ℝ ∞ (homogeneousAngularProjection a N ha ha1 hk h u) (Ioi R))
    (β c : ℝ) (hβ : -6 ≤ β) (hc : 0 ≤ c)
    (hlim : Tendsto (fun r =>
      ‖iteratedDeriv N (homogeneousAngularProjection a N ha ha1 hk h u) r‖ / r ^ β)
      atTop (𝓝 c)) : c = 0 :=
  radial_weighted_limit_eq_zero _ R β c hβ hc
    (homogeneousAngularProjection_iteratedDeriv_integrable a N ha ha1 hk h hh u R hR hsmooth)
    hlim

end DefocusingNLS

end OAI
