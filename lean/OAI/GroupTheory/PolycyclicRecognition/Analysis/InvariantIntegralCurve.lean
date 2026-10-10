import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialIntegralCurve
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

namespace OAI

/-! # Global integral curves of left-invariant vector fields -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

omit [FiniteDimensional ℝ E] in
theorem mulInvariantVectorField_mul
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (a x : G) :
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) x)
      (mulInvariantVectorField v x) = mulInvariantVectorField v (a * x) := by
  have hf : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => x * g) 1 :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := x) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun g : G => x * g)).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (x * 1) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := a) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun g : G => a * g)).mdifferentiableAt (by simp)
  have hc := mfderiv_comp (I' := 𝓘(ℝ, E)) 1 hg hf
  have heq : (fun g : G => a * g) ∘ (fun g : G => x * g) = fun g => (a * x) * g := by
    ext g
    exact (mul_assoc a x g).symm
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      ((fun g : G => a * g) ∘ (fun g : G => x * g)) 1 : E →L[ℝ] E) =
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (x * 1) : E →L[ℝ] E).comp
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => x * g) 1) at hc
  rw [heq] at hc
  have h := congrArg (fun L : E →L[ℝ] E => L v) hc
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => (a * x) * g) 1) v =
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (x * 1))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => x * g) 1) v) at h
  have hx : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (x * 1) : E →L[ℝ] E) =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) x : E →L[ℝ] E) := by
    congr 1
    exact mul_one x
  rw [hx] at h
  exact h.symm

omit [FiniteDimensional ℝ E] in
theorem IsMIntegralCurveOn.mul_left_invariant
    {γ : ℝ → G} {s : Set ℝ} {v : GroupLieAlgebra (𝓘(ℝ, E)) G}
    (hγ : IsMIntegralCurveOn (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v) s) (a : G) :
    IsMIntegralCurveOn (I := 𝓘(ℝ, E)) (fun t => a * γ t) (mulInvariantVectorField v) s := by
  intro t ht
  have ha : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (γ t) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := a) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun g : G => a * g)).mdifferentiableAt (by simp)
  apply (ha.hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  let u : ℝ := r
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (γ t))
      (u • mulInvariantVectorField v (γ t)) = u • mulInvariantVectorField v (a * γ t)
  rw [map_smul, mulInvariantVectorField_mul]

/-- A fixed local existence time at the identity works at every point by
left translation, so the manifold uniform-time theorem supplies global curves. -/
theorem exists_global_invariant_integralCurve [T2Space G]
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (x : G) :
    ∃ γ : ℝ → G, γ 0 = x ∧ IsMIntegralCurve (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v) := by
  have hv : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) 1
      (fun g : G => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle (𝓘(ℝ, E)) G)) :=
    (contMDiff_mulInvariantVectorField v).of_le (by norm_num)
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (I := 𝓘(ℝ, E)) (x₀ := (1 : G)) 0 hv.contMDiffAt
  obtain ⟨ε, hε, hγon⟩ := isMIntegralCurveAt_iff'.mp hγ
  have hγI : IsMIntegralCurveOn (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v)
      (Set.Ioo (-ε) ε) := by
    simpa only [Real.ball_eq_Ioo, sub_zero, zero_sub, zero_add] using hγon
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε _ x
  intro y
  exact ⟨fun t => y * γ t, by simp [hγ0],
    PolycyclicRecognition.IsMIntegralCurveOn.mul_left_invariant hγI y⟩

end PolycyclicRecognition

end

end OAI
