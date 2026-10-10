import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousResolventCircle
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Exchanging the two compact contour integrals

Only centered circles are needed for the time-step spectral projection.
-/

open Complex Set MeasureTheory

namespace DefocusingNLS

theorem circleIntegral_swap {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℂ A] [CompleteSpace A] {f : ℂ × ℂ → A} {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hf : ContinuousOn f (Metric.sphere 0 r ×ˢ Metric.sphere 0 R)) :
    (∮ z in C(0, r), ∮ w in C(0, R), f (z, w)) =
      ∮ w in C(0, R), ∮ z in C(0, r), f (z, w) := by
  let g : ℝ × ℝ → A := fun p =>
    (deriv (circleMap 0 r) p.1 * deriv (circleMap 0 R) p.2) •
      f (circleMap 0 r p.1, circleMap 0 R p.2)
  have hmap : Continuous (fun p : ℝ × ℝ => (circleMap 0 r p.1, circleMap 0 R p.2)) := by
    fun_prop
  have hg : ContinuousOn g (Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi)) := by
    apply ContinuousOn.smul
    · simp only [deriv_circleMap]
      fun_prop
    · apply hf.comp hmap.continuousOn
      intro p _
      exact ⟨circleMap_mem_sphere 0 hr p.1, circleMap_mem_sphere 0 hR p.2⟩
  have hi : IntegrableOn g (Set.uIoc 0 (2 * Real.pi) ×ˢ Set.uIoc 0 (2 * Real.pi)) := by
    apply (hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    simpa only [Set.uIoc_of_le Real.two_pi_pos.le] using
      Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F := fun θ φ => g (θ, φ)) hi
  simpa only [circleIntegral, ← intervalIntegral.integral_smul, smul_smul, g,
    mul_comm (deriv (circleMap 0 R) _) (deriv (circleMap 0 r) _)] using hswap

end DefocusingNLS

end OAI
