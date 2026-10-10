import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingMovingCutoff
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarInput

namespace OAI

/-! Sufficiently large compact tests are identically one on the common
support of the finite-time drift and source. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows ExpandingDetector Set
open scoped ContDiff

theorem CompactPlaneCoefficients.cutoff_eventually_exact
    {a : ℝ → Plane → Plane} {h : ℝ → Plane → ℝ}
    (hc : CompactPlaneCoefficients a h) (T : ℝ) (hT : 0 ≤ T) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc 0 T, ∀ x,
      fderiv ℝ (concentrationCutoff ((n : ℝ) + 1) 0) x (a t x) = 0 ∧
        concentrationCutoff ((n : ℝ) + 1) 0 x * h t x = h t x := by
  obtain ⟨K, hK, hz⟩ := hc T hT
  obtain ⟨B, hB⟩ := hK.bddAbove_image (continuous_norm.continuousOn : ContinuousOn (fun x : Plane => ‖x‖) K)
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * max 0 B)
  refine ⟨N, ?_⟩
  intro n hn t ht x
  by_cases hx : x ∈ K
  · have hxn : ‖x‖ ≤ B := hB (mem_image_of_mem _ hx)
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have he := concentrationCutoff_one_near (c := (0 : Plane)) hr (x := x) (by
      intro j
      have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
      simp only [Pi.zero_apply, sub_zero]
      linarith [le_max_right (0 : ℝ) B])
    have hd : fderiv ℝ (concentrationCutoff ((n : ℝ) + 1) 0) x = 0 := by
      rw [he.fderiv_eq]
      exact fderiv_const_apply (1 : ℝ)
    exact ⟨by rw [hd]; rfl, by rw [he.eq_of_nhds, one_mul]⟩
  · obtain ⟨ha, hh⟩ := hz t ht x hx
    rw [ha, hh, map_zero, mul_zero]
    exact ⟨rfl, rfl⟩

end ForcedComputation.VelocityDetector

end

end OAI
