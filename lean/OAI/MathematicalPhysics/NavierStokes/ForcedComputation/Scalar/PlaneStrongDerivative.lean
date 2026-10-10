import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneSquareContinuity
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! Pointwise differentiation and a common L2 derivative envelope imply
strong L2 differentiation, including one-sided differentiation at time zero. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set Filter
open scoped Topology

def PlaneStrongDerivativeOn (F G : ℝ → Plane → ℝ) (S : Set ℝ) : Prop :=
  ∀ t ∈ S, Tendsto
    (fun s => ∫ x, (slope (fun r => F r x) t s - G t x) ^ 2)
    (𝓝[S \ {t}] t) (𝓝 0)

theorem strongDerivativeOn_of_envelope {F G : ℝ → Plane → ℝ} {S : Set ℝ}
    (hS : Convex ℝ S) {b : Plane → ℝ}
    (hspace : ∀ t ∈ S, Continuous (F t))
    (hgspace : ∀ t ∈ S, Continuous (G t))
    (hd : ∀ t ∈ S, ∀ x, HasDerivWithinAt (fun r => F r x) (G t x) S t)
    (hb : Integrable (fun x => b x ^ 2))
    (hbound : ∀ t ∈ S, ∀ x, |G t x| ≤ b x) :
    PlaneStrongDerivativeOn F G S := by
  intro t ht
  have hmeas : ∀ᶠ s in 𝓝[S \ {t}] t,
      AEStronglyMeasurable (fun x => (slope (fun r => F r x) t s - G t x) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hc : Continuous (fun x => slope (fun r => F r x) t s - G t x) := by
      simp only [slope_def_field]
      exact (((hspace s hs.1).sub (hspace t ht)).div_const (s - t)).sub (hgspace t ht)
    exact (hc.pow 2).aestronglyMeasurable
  have hmajor : ∀ᶠ s in 𝓝[S \ {t}] t, ∀ᵐ x,
      ‖(slope (fun r => F r x) t s - G t x) ^ 2‖ ≤ 4 * b x ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [] with x
    have hst : s ≠ t := by simpa only [mem_singleton_iff] using hs.2
    have hb0 : 0 ≤ b x := (abs_nonneg _).trans (hbound t ht x)
    have hl := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr => hd r hr x)
      (fun r hr => show ‖G r x‖ ≤ b x by simpa only [Real.norm_eq_abs] using hbound r hr x)
      hS ht hs.1
    have hq : |slope (fun r => F r x) t s| ≤ b x := by
      rw [slope_def_field, abs_div]
      apply (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hst))).mpr
      simpa only [Real.norm_eq_abs] using hl
    have he : |slope (fun r => F r x) t s - G t x| ≤ 2 * b x :=
      (abs_sub _ _).trans (by linarith [hbound t ht x])
    have he2 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * b x)).mpr he
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (slope (fun r => F r x) t s - G t x)]
  have hlim : ∀ᵐ x, Tendsto
      (fun s => (slope (fun r => F r x) t s - G t x) ^ 2)
      (𝓝[S \ {t}] t) (𝓝 (0 : ℝ)) := by
    filter_upwards [] with x
    have hh := ((hasDerivWithinAt_iff_tendsto_slope.mp (hd t ht x)).sub_const (G t x)).pow 2
    simpa using hh
  have he := tendsto_integral_filter_of_dominated_convergence (f := fun _ : Plane => (0 : ℝ))
    (fun x => 4 * b x ^ 2)
    hmeas hmajor (hb.const_mul 4) hlim
  simpa using he

end ForcedComputation.VelocityDetector

end

end OAI
