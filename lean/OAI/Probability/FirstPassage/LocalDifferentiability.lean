import OAI.Probability.FirstPassage.ExtremeSlopes
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace OAI

namespace PlanarFPP
open Set Filter
open scoped Topology

theorem profile_hasDerivAt_of_equal_slopes (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ)
    (heq : leftSlope φ = rightSlope φ) : HasDerivAt φ (leftSlope φ) 0 := by
  obtain ⟨hl, hr⟩ := extreme_slopes_contact φ hφ
  rw [← heq] at hr
  apply hasDerivAt_iff_tendsto_slope_left_right.mpr
  exact ⟨(hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hl,
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hr⟩

theorem differentiableAt_of_transverse_profile
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : E → ℝ) (x r : E →L[ℝ] ℝ) (u e : E)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hru : r u = 0)
    (hcoords : ∀ z, z = x z • u + r z • e)
    (hprofile : DifferentiableAt ℝ (fun t : ℝ => μ (u + t • e)) 0) :
    DifferentiableAt ℝ μ u := by
  let φ : ℝ → ℝ := fun t => μ (u + t • e)
  have hinv : DifferentiableAt ℝ (fun z : E => (x z)⁻¹) u :=
    (hasDerivAt_inv (x := x u) (by rw [hxu]; norm_num)).differentiableAt.comp u x.differentiableAt
  have hquot : DifferentiableAt ℝ (fun z : E => r z / x z) u := by
    convert! r.differentiableAt.mul hinv using 1
  have hcomp : DifferentiableAt ℝ (fun z : E => φ (r z / x z)) u := by
    have hφat : DifferentiableAt ℝ φ (r u / x u) := by
      simpa only [hru, hxu, zero_div] using hprofile
    exact DifferentiableAt.comp (f := fun z : E => r z / x z) (g := φ) u hφat hquot
  have hprod : DifferentiableAt ℝ (fun z : E => x z * φ (r z / x z)) u :=
    x.differentiableAt.mul hcomp
  have hpos : ∀ᶠ z in 𝓝 u, 0 < x z :=
    x.continuous.continuousAt (lt_mem_nhds (show 0 < x u by rw [hxu]; norm_num))
  have heq : μ =ᶠ[𝓝 u] (fun z : E => x z * φ (r z / x z)) := by
    filter_upwards [hpos] with z hz
    have hrepr : z = x z • (u + (r z / x z) • e) := by
      rw [smul_add, smul_smul]
      have hc : x z * (r z / x z) = r z := by field_simp [ne_of_gt hz]
      rw [hc]
      exact hcoords z
    change μ z = x z * μ (u + (r z / x z) • e)
    conv_lhs => rw [hrepr]
    exact hhom _ (le_of_lt hz) _
  exact hprod.congr_of_eventuallyEq heq

theorem differentiableAt_of_equal_extreme_slopes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : E → ℝ) (x r : E →L[ℝ] ℝ) (u e : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hru : r u = 0)
    (hcoords : ∀ z, z = x z • u + r z • e)
    (heq : leftSlope (fun t : ℝ => μ (u + t • e)) =
      rightSlope (fun t : ℝ => μ (u + t • e))) :
    ∃ ℓ : E →L[ℝ] ℝ, HasFDerivAt μ ℓ u := by
  exact differentiableAt_of_transverse_profile μ x r u e hhom hxu hru hcoords
    (profile_hasDerivAt_of_equal_slopes _ (convex_transverse_profile μ u e hadd hhom)
      heq).differentiableAt

end PlanarFPP

end OAI
