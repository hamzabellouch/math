import OAI.Analysis.CircleDomains.Selection.MeanGeometricIndex
import OAI.Analysis.CircleDomains.Topology.BoundaryIndexMean

namespace OAI

/-! The actual mean index has the previously constructed positive
Stieltjes boundary coordinate for the actual starting-angle law. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem translatedHalfPlaneRay_start (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) :
    (translatedHalfPlaneRay γ hγ k).curve ⟨0, bot_lt_top⟩ =
      ((circleRepresentative (normalizedArgument (γ 0)) + (k : ℝ) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [translatedHalfPlaneRay, ContinuousMap.coe_mk, Complex.add_re,
      Complex.intCast_re, diskRayComplex, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, diskRayAngle_zero]
  · simpa only [Complex.ofReal_im] using (translatedHalfPlaneRay γ hγ k).start

 theorem geometricRayIndex_boundary_of_avoids (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (x : ℝ)
    (hx : diskRayProjection (x : ℂ) ∉ range γ) :
    geometricRayIndex hsch γ hγ (x : ℂ) =
      ⌊x - circleRepresentative (normalizedArgument (γ 0))⌋ := by
  apply geometricRayIndex_boundary_floor hsch γ hγ x
  intro k hk
  apply hx
  refine ⟨0, ?_⟩
  rw [hk, ← translatedHalfPlaneRay_start γ hγ k,
    diskRayProjection_translated]

 def compactArcStartingAngleLaw (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure K) :
    ProbabilityMeasure UnitAddCircle := η.map (fun γ : K => normalizedArgument (γ.val 0))

 theorem measurable_compactArcStartingAngle (K : Set C(PathTime, ℂ)) :
    Measurable (fun γ : K => normalizedArgument (γ.val 0)) :=
  measurable_normalizedArgument.comp ((continuous_eval_const 0).comp continuous_subtype_val).measurable

 theorem meanGeometricIndex_boundary (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (x : ℝ)
    (hx : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (x : ℂ) ∉ range γ.val) :
    meanGeometricIndex hsch K hKS η ⟨(x : ℂ), by simp⟩ =
      boundaryIndexMean (compactArcStartingAngleLaw K η) x := by
  have he : (fun γ : K => (geometricRayIndex hsch γ.val (hKS γ.property) (x : ℂ) : ℝ)) =ᵐ[(η : Measure K)]
      fun γ => (⌊x - circleRepresentative (normalizedArgument (γ.val 0))⌋ : ℝ) := by
    filter_upwards [hx] with γ hγ
    rw [geometricRayIndex_boundary_of_avoids hsch γ.val (hKS γ.property) x hγ]
  rw [meanGeometricIndex, integral_congr_ae he]
  symm
  rw [boundaryIndexMean, compactArcStartingAngleLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_compactArcStartingAngle K).aemeasurable
      (measurable_boundaryIndex x).aestronglyMeasurable]
  rfl

end CircleDomainRigidity

end

end OAI
