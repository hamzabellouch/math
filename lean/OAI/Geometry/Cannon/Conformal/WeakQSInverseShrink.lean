import Mathlib
import OAI.Geometry.Cannon.Conformal.PreservesProducts

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Topology

noncomputable section
open Set Metric Filter Topology

noncomputable section
open Set Filter Topology Metric

noncomputable section
open Set Filter Topology
open MeasureTheory
open scoped ENNReal

noncomputable section
open Set Metric Filter Topology

noncomputable section
open MeasureTheory Filter Set Metric Function ContinuousLinearMap
open scoped Topology Convolution ContDiff Pointwise

noncomputable section
namespace CannonMetricQC
open Metric

lemma weakQS_of_inverse_shrink (f : ℂ ≃ₜ ℂ) {η : ℝ} (hη : 0 < η)
    (hs : ∀ x a b : ℂ, b ≠ x → dist a x < η*dist b x →
      dist (f.symm a) (f.symm x) ≤ (1/2:ℝ)*dist (f.symm b) (f.symm x)) :
    WeakQS f η⁻¹ := by
  intro x a b hab
  by_cases ha : a=x
  · rw [ha,dist_self]
    positivity
  have hp : 0 < dist a x := dist_pos.mpr ha
  have hpx : f a ≠ f x := fun h => ha (f.injective h)
  have h : η*dist (f a) (f x) ≤ dist (f b) (f x) := by
    by_contra! hn
    have hh := hs (f x) (f b) (f a) hpx hn
    simp only [f.symm_apply_apply] at hh
    rw [dist_comm x a,dist_comm x b] at hab
    linarith
  have he : dist (f a) (f x) ≤ dist (f b) (f x)/η := (le_div_iff₀ hη).mpr (by nlinarith [h])
  simpa only [div_eq_mul_inv,mul_comm,dist_comm] using he
end CannonMetricQC

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
