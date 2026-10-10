import OAI.GroupTheory.PolycyclicRecognition.Analysis.InvariantIntegralCurve

namespace OAI

/-! # Construction of the intrinsic Lie exponential from global integral curves -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

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
  exact PolycyclicRecognition.IsMIntegralCurveOn.mul_left_invariant hγ a

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

end PolycyclicRecognition

end

end OAI
