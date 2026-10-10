import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalMeasurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! # Bochner integrability of bounded physical limits on finite time slabs -/

open Set MeasureTheory

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem stronglyMeasurable_homogeneous_clamped (a k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (u : Icc (0 : ℝ) T → HomogeneousY a k)
    (hp : ∀ y : E, Continuous (fun t => homogeneousPhysicalCLM a k ha ha1 hk (u t) y)) :
    StronglyMeasurable (fun t : ℝ => u (projIcc 0 T hT t)) := by
  apply stronglyMeasurable_of_homogeneousPhysical a k ha ha1 hk
  intro y
  exact ((hp y).comp continuous_projIcc).measurable

theorem integrableOn_homogeneous_clamped (a k T M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (u : Icc (0 : ℝ) T → HomogeneousY a k) (hu : ∀ t, ‖u t‖ ≤ M)
    (hp : ∀ y : E, Continuous (fun t => homogeneousPhysicalCLM a k ha ha1 hk (u t) y)) :
    IntegrableOn (fun t : ℝ => u (projIcc 0 T hT t)) (Icc 0 T) := by
  have hb : IntegrableOn (fun _ : ℝ => M) (Icc 0 T) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  exact hb.mono' (stronglyMeasurable_homogeneous_clamped a k T ha ha1 hk hT u hp).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => hu (projIcc 0 T hT t)))

end DefocusingNLS

end OAI
