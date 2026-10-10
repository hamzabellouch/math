import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothRotationalTwist
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PullbackTangentCoordinates

namespace OAI

/-! # The invariant frame of the rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  (α : K →* MulAut G) (τ : G →* K)
  (hinv : ∀ k g, τ (α k g) = τ g) [hτ : Fact (Continuous τ)]
  (hα : ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
    (fun p : G × G => α ((τ p.1)⁻¹) p.2))

attribute [local instance] semidirectProductTopology
local instance : ChartedSpace E (rotationalTwist α τ hinv) :=
  rotationalTwistChartedSpace α τ hinv
include hα in
theorem rotationalTwist_invariant_field
    (p : rotationalTwist α τ hinv)
    (v : GroupLieAlgebra (𝓘(ℝ,E)) (rotationalTwist α τ hinv)) :
    mulInvariantVectorField v p =
      mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun y : G => p.val.left * y) 1
        (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (α ((τ p.val.left)⁻¹)) 1 v) := by
  let : LieGroup (𝓘(ℝ,E)) ∞ (rotationalTwist α τ hinv) :=
    rotationalTwistLieGroup α τ hinv hα
  let e := rotationalTwistHomeomorph α τ hinv hτ.out
  have he1 : e (1 : rotationalTwist α τ hinv) = 1 := rfl
  have he : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ e :=
    contMDiff_rotationalTwistProjection α τ hinv
  have ha : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (α ((τ p.val.left)⁻¹)) := by
    have hpair : ContMDiff (𝓘(ℝ,E)) ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) ∞
        (fun y : G => (p.val.left,y)) := contMDiff_const.prodMk contMDiff_id
    simpa only [Function.comp_def] using hα.comp hpair
  have hp : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E))
      (fun q : rotationalTwist α τ hinv => p*q) 1 :=
    (contMDiff_mul_left (I := 𝓘(ℝ,E)) (n := ∞)).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E))
      (fun y : G => p.val.left*y) 1 :=
    (contMDiff_mul_left (I := 𝓘(ℝ,E)) (n := ⊤)).mdifferentiableAt (by simp)
  have hleft := mfderiv_comp (I' := 𝓘(ℝ,E)) 1
    (he.mdifferentiableAt (x := p*1) (by simp)) hp
  have ha1 := ha.mdifferentiableAt (x := (1 : G)) (by simp)
  have hl' : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E))
      (fun y : G => p.val.left*y) (α ((τ p.val.left)⁻¹) 1) := by
    simpa only [map_one] using hl
  have hr := hl'.hasMFDerivAt.comp (1 : rotationalTwist α τ hinv)
    ((ha1.hasMFDerivAt.comp (1 : rotationalTwist α τ hinv)
      (he.mdifferentiableAt (x := 1) (by simp)).hasMFDerivAt))
  have hfun : e ∘ (fun q : rotationalTwist α τ hinv => p*q) =
      (fun y : G => p.val.left*y) ∘ (α ((τ p.val.left)⁻¹)) ∘ e := by
    funext q
    change p.val.left * α p.val.right q.val.left =
      p.val.left * α ((τ p.val.left)⁻¹) q.val.left
    rw [p.property]
  rw [hfun] at hleft
  have hD := hleft.symm.trans hr.mfderiv
  have hep : mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) e (p*1) = ContinuousLinearMap.id ℝ E :=
    mfderiv_pullback e (p*1)
  have he0 : mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) e 1 = ContinuousLinearMap.id ℝ E :=
    mfderiv_pullback e 1
  change (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) e (p*1) : E →L[ℝ] E).comp
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun q => p*q) 1 : E →L[ℝ] E) =
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun y : G => p.val.left*y)
      (α ((τ p.val.left)⁻¹) 1) : E →L[ℝ] E).comp
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (α ((τ p.val.left)⁻¹)) 1 : E →L[ℝ] E).comp
        (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) e 1 : E →L[ℝ] E)) at hD
  have hv := congrArg (fun A : E →L[ℝ] E => A v) hD
  change (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) e (p*1))
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun q => p*q) 1) v) =
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun y : G => p.val.left*y)
      (α ((τ p.val.left)⁻¹) 1))
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (α ((τ p.val.left)⁻¹)) 1)
        ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) e 1) v)) at hv
  rw [hep,he0] at hv
  change mulInvariantVectorField v p =
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun y : G => p.val.left*y)
      (α ((τ p.val.left)⁻¹) 1))
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (α ((τ p.val.left)⁻¹)) 1) v) at hv
  have hpoint : α ((τ p.val.left)⁻¹) (1 : G) = 1 := (α ((τ p.val.left)⁻¹)).map_one
  rw [hpoint] at hv
  exact hv

end PolycyclicRecognition

end

end OAI
