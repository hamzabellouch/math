import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieExponential
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

namespace OAI

/-! # The intrinsic exponential for the smooth rotational graph

The same invariant-field ODE construction works at C-infinity regularity.
This concrete version avoids imposing an analytic atlas on the new graph.
-/

noncomputable section
namespace PolycyclicRecognition.SmoothLie
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ∞ G]

local instance : LieGroup (𝓘(ℝ,E)) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (n := ∞) (by simp)

omit [FiniteDimensional ℝ E] in
theorem mulInvariantVectorField_mul
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (a x : G) :
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) x)
      (mulInvariantVectorField v x) = mulInvariantVectorField v (a * x) := by
  have hf : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => x * g) 1 :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := x) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun g : G => x * g)).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (x * 1) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := a) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun g : G => a * g)).mdifferentiableAt (by simp)
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
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun g : G => a * g)).mdifferentiableAt (by simp)
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
    PolycyclicRecognition.SmoothLie.IsMIntegralCurveOn.mul_left_invariant hγI y⟩


variable [T2Space G]

omit [FiniteDimensional ℝ E] in
theorem invariant_integralCurve_unique
    {v : GroupLieAlgebra (𝓘(ℝ, E)) G} {γ δ : ℝ → G}
    (hγ : IsMIntegralCurve (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v))
    (hδ : IsMIntegralCurve (I := 𝓘(ℝ, E)) δ (mulInvariantVectorField v))
    (hzero : γ 0 = δ 0) : γ = δ := by
  have hv : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) 1
      (fun g : G => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle (𝓘(ℝ, E)) G)) :=
    (contMDiff_mulInvariantVectorField v).of_le (by norm_num)
  exact isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv hγ hδ hzero

omit [FiniteDimensional ℝ E] [T2Space G] in
theorem invariant_integralCurve_mul_left
    {v : GroupLieAlgebra (𝓘(ℝ, E)) G} {γ : ℝ → G}
    (hγ : IsMIntegralCurve (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v)) (a : G) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) (fun t => a * γ t) (mulInvariantVectorField v) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
  exact PolycyclicRecognition.SmoothLie.IsMIntegralCurveOn.mul_left_invariant hγ a

/-- The global integral curve starting at the identity. Its independence of
the existence theorem's choice follows from ODE uniqueness. -/
def invariantCurve (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : ℝ → G :=
  (exists_global_invariant_integralCurve v (1 : G)).choose

@[simp] theorem invariantCurve_zero (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    invariantCurve v 0 = 1 :=
  (exists_global_invariant_integralCurve v (1 : G)).choose_spec.1

theorem invariantCurve_isMIntegralCurve (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) (invariantCurve v) (mulInvariantVectorField v) :=
  (exists_global_invariant_integralCurve v (1 : G)).choose_spec.2

theorem invariantCurve_smul (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (s : ℝ) :
    invariantCurve (s • v) = invariantCurve v ∘ (· * s) := by
  apply invariant_integralCurve_unique (invariantCurve_isMIntegralCurve (s • v))
  · simpa only [mulInvariantVectorField_smul] using
      (invariantCurve_isMIntegralCurve v).comp_mul s
  · simp

theorem invariantCurve_add (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (s t : ℝ) :
    invariantCurve v (s + t) = invariantCurve v s * invariantCurve v t := by
  have heq := invariant_integralCurve_unique
    ((invariantCurve_isMIntegralCurve v).comp_add s)
    (invariant_integralCurve_mul_left (invariantCurve_isMIntegralCurve v) (invariantCurve v s))
    (by simp)
  simpa only [Function.comp_apply, add_comm] using congrFun heq t

/-- The intrinsic exponential, constructed without a Lie-theoretic existence input. -/
def groupExponential (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : G := invariantCurve v 1

theorem groupExponential_smul (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (s : ℝ) :
    groupExponential (s • v) = invariantCurve v s := by
  simpa only [groupExponential, Function.comp_apply, one_mul] using
    congrFun (invariantCurve_smul v s) 1

/-- Existence of the Lie exponential with its one-parameter subgroup law and
its specified tangent vector at zero. -/
theorem groupExponential_isGroupExponential :
    IsGroupExponential (groupExponential (E := E) (G := G)) where
  map_zero := by
    have h := groupExponential_smul (0 : GroupLieAlgebra (𝓘(ℝ, E)) G) 0
    simpa only [zero_smul, invariantCurve_zero] using h
  map_add_smul v s t := by
    simp only [groupExponential_smul, invariantCurve_add]
  hasMFDerivAt_zero v := by
    have hv : mulInvariantVectorField v (1 : G) = v := by
      unfold mulInvariantVectorField
      rw [show (fun x : G => 1 * x) = id from funext one_mul, mfderiv_id]
      rfl
    have hfun : (fun t : ℝ => groupExponential (t • v)) = invariantCurve v :=
      funext (groupExponential_smul v)
    rw [hfun]
    apply (invariantCurve_isMIntegralCurve v 0).congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    let s : ℝ := r
    change s • mulInvariantVectorField v (invariantCurve v 0) = s • v
    congr 1
    have heq : (mulInvariantVectorField v (invariantCurve v 0) : E) =
        (mulInvariantVectorField v 1 : E) := by
      congr 1
      exact invariantCurve_zero v
    exact heq.trans hv

theorem exists_groupExponential :
    ∃ Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G, IsGroupExponential Exp :=
  ⟨groupExponential, groupExponential_isGroupExponential⟩


end PolycyclicRecognition.SmoothLie

end

end OAI
