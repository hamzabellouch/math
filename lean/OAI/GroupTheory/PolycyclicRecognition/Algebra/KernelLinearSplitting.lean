import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # The linear splitting used by the height-kernel product

The tangent inclusion onto the height kernel, together with any continuous
linear right inverse of height, gives an invertible product differential.
-/

noncomputable section
namespace PolycyclicRecognition

variable {U V W : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem kernel_coprod_bijective
    (j : U →L[ℝ] V) (d : V →L[ℝ] W) (l : W →L[ℝ] V)
    (hj : Function.Injective j)
    (hrange : LinearMap.range j.toLinearMap = LinearMap.ker d.toLinearMap)
    (hdl : d.comp l = ContinuousLinearMap.id ℝ W) :
    Function.Bijective (j.coprod l) := by
  have hdj (u : U) : d (j u) = 0 := by
    have hu : j u ∈ LinearMap.range j.toLinearMap := ⟨u, rfl⟩
    rwa [hrange] at hu
  have hdl' (w : W) : d (l w) = w := congrArg (fun F : W →L[ℝ] W => F w) hdl
  constructor
  · intro a b hab
    have hw : a.2 = b.2 := by
      have h := congrArg d hab
      change d (j a.1 + l a.2) = d (j b.1 + l b.2) at h
      simpa only [map_add, hdj, hdl', zero_add] using h
    apply Prod.ext _ hw
    apply hj
    change j a.1 + l a.2 = j b.1 + l b.2 at hab
    rw [hw] at hab
    exact add_right_cancel hab
  · intro v
    have hv : v - l (d v) ∈ LinearMap.range j.toLinearMap := by
      rw [hrange]
      change d (v - l (d v)) = 0
      rw [map_sub, hdl', sub_self]
    obtain ⟨u, hu⟩ := hv
    refine ⟨(u, d v), ?_⟩
    change j u = v - l (d v) at hu
    change j u + l (d v) = v
    rw [hu, sub_add_cancel]

end PolycyclicRecognition

end

end OAI
