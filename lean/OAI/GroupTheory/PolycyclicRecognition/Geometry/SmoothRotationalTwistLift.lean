import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationalTwistLift
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PullbackTangentCoordinates

namespace OAI

/-! # Smooth subgroup lifts into the rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {V E A G K : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group A] [TopologicalSpace A] [ChartedSpace V A]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [IsManifold (𝓘(ℝ,E)) ∞ G]
  [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  (α : K →* MulAut G) (τ : G →* K)
  (hinv : ∀ k g, τ (α k g) = τ g) [hτ : Fact (Continuous τ)]
  (f : A →* G) (hfix : ∀ a b, α ((τ (f a))⁻¹) (f b) = f b)

attribute [local instance] semidirectProductTopology

local instance rotationalTwistLiftChartedSpace : ChartedSpace E (rotationalTwist α τ hinv) :=
  pullbackChartedSpace (rotationalTwistHomeomorph α τ hinv hτ.out)

omit [IsManifold (𝓘(ℝ,E)) ∞ G] in
theorem contMDiff_rotationalTwistLift
    (hf : ContMDiff (𝓘(ℝ,V)) (𝓘(ℝ,E)) ∞ f) :
    ContMDiff (𝓘(ℝ,V)) (𝓘(ℝ,E)) ∞ (rotationalTwistLift α τ hinv f hfix) := by
  exact (contMDiff_pullback_symm (E := E)
    (rotationalTwistHomeomorph α τ hinv hτ.out)).comp hf

/-- In the pulled-back atlas, lifting changes no tangent coordinates. -/
theorem mfderiv_rotationalTwistLift
    (hf : ContMDiff (𝓘(ℝ,V)) (𝓘(ℝ,E)) ∞ f) (a : A) (v : V) :
    mfderiv (𝓘(ℝ,V)) (𝓘(ℝ,E)) (rotationalTwistLift α τ hinv f hfix) a v =
      mfderiv (𝓘(ℝ,V)) (𝓘(ℝ,E)) f a v := by
  let e := rotationalTwistHomeomorph α τ hinv hτ.out
  have hd := mfderiv_comp (I' := 𝓘(ℝ,E)) a
    ((contMDiff_pullback_symm (E := E) e).mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  have hv := congrArg (fun D : V →L[ℝ] E => D v) hd
  change mfderiv (𝓘(ℝ,V)) (𝓘(ℝ,E)) (rotationalTwistLift α τ hinv f hfix) a v =
    mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) e.symm (f a)
      (mfderiv (𝓘(ℝ,V)) (𝓘(ℝ,E)) f a v) at hv
  rw [mfderiv_pullback_symm] at hv
  exact hv

end PolycyclicRecognition

end

end OAI
