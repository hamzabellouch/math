import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConstructExponential

namespace OAI

/-! # Naturality of the intrinsic exponential

The exponential compatibility clause of Lie integration follows from the
chain rule and uniqueness of invariant integral curves. No integration
theorem or representation theorem is used here.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]

theorem mfderiv_hom_invariant (φ : G →* H)
    (hφ : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (g : G) :
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ g) (mulInvariantVectorField v g) =
      mulInvariantVectorField ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v) (φ g) := by
  have hleft : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) 1 :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := g) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun x : G => g * x)).mdifferentiableAt (by simp)
  have hright : MDifferentiableAt (𝓘(ℝ, F)) (𝓘(ℝ, F))
      (fun y : H => φ g * y) (φ 1) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, F)) (a := φ g) :
      ContMDiff (𝓘(ℝ, F)) (𝓘(ℝ, F)) ⊤ (fun y : H => φ g * y)).mdifferentiableAt (by simp)
  have h₁ := mfderiv_comp (I' := 𝓘(ℝ, E)) 1 (hφ (g * 1)) hleft
  have h₂ := mfderiv_comp (I' := 𝓘(ℝ, F)) 1 hright (hφ 1)
  have heq : φ ∘ (fun x : G => g * x) = (fun y : H => φ g * y) ∘ φ := by
    funext x
    exact φ.map_mul g x
  rw [heq] at h₁
  have hmaps : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ (g * 1) : E →L[ℝ] F) =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ g : E →L[ℝ] F) := by
    congr 1
    exact mul_one g
  have hmapt : (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) (fun y : H => φ g * y) (φ 1) : F →L[ℝ] F) =
      (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) (fun y : H => φ g * y) 1 : F →L[ℝ] F) := by
    congr 1
    exact φ.map_one
  have h := congrArg (fun L : E →L[ℝ] F => L v) (h₁.symm.trans h₂)
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ (g * 1))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) 1) v) =
    (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) (fun y : H => φ g * y) (φ 1))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v) at h
  rw [hmaps, hmapt] at h
  exact h

theorem invariant_integralCurve_map (φ : G →* H)
    (hφ : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ)
    {v : GroupLieAlgebra (𝓘(ℝ, E)) G} {γ : ℝ → G}
    (hγ : IsMIntegralCurve (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v)) :
    IsMIntegralCurve (I := 𝓘(ℝ, F)) (φ ∘ γ)
      (mulInvariantVectorField ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v)) := by
  intro t
  apply ((hφ (γ t)).hasMFDerivAt.comp t (hγ t)).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  let s : ℝ := r
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ (γ t))
      (s • mulInvariantVectorField v (γ t)) =
    s • mulInvariantVectorField ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v) (φ (γ t))
  rw [map_smul, mfderiv_hom_invariant φ hφ]

/-- Every differentiable homomorphism commutes with the intrinsic exponential. -/
theorem IsGroupExponential.map_of_mdifferentiable [T2Space H]
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (hG : IsGroupExponential ExpG) (hH : IsGroupExponential ExpH)
    (φ : G →* H) (hφ : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    φ (ExpG v) = ExpH ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v) := by
  let w : GroupLieAlgebra (𝓘(ℝ, F)) H := (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v
  have hmap : IsMIntegralCurve (I := 𝓘(ℝ, F))
      (φ ∘ fun t : ℝ => ExpG (t • v)) (mulInvariantVectorField w) :=
    invariant_integralCurve_map φ hφ (hG.isMIntegralCurve v)
  have heq := invariant_integralCurve_unique hmap (hH.isMIntegralCurve w)
    (by simp only [Function.comp_apply, zero_smul, hG.map_zero, hH.map_zero, map_one])
  have ht := congrFun heq 1
  change φ (ExpG (1 • v)) = ExpH (1 • w) at ht
  simpa only [one_smul] using ht

end PolycyclicRecognition

end

end OAI
