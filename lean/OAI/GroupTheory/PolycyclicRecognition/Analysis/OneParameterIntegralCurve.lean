import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConstructExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieProductDifferential

namespace OAI

/-! # Recovering a one-parameter subgroup from its tangent vector -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem oneParameter_isMIntegralCurve {γ : ℝ → G}
    (hzero : γ 0 = 1) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hd : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ 0
      ((ContinuousLinearMap.id ℝ ℝ).smulRight v)) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v) := by
  intro t
  have hbase : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (t - t)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight v) := by rw [sub_self]; exact hd
  have hshift : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun s : ℝ => s - t) t
      (ContinuousLinearMap.id ℝ ℝ) := by
    have hD : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) =
        ContinuousLinearMap.id ℝ ℝ := by ext; simp
    simpa only [id_eq, hD] using ((hasDerivAt_id t).sub_const t).hasFDerivAt.hasMFDerivAt
  have hl : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g)
      (γ (t - t)) (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) := by
    rw [sub_self, hzero]
    exact (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := γ t) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun g : G => γ t * g)).mdifferentiableAt
        (by simp) |>.hasMFDerivAt
  have hh := hl.comp t (HasMFDerivAt.comp t (f := fun s : ℝ => s - t) hbase hshift)
  have heq : (fun s : ℝ => γ t * γ (s - t)) = γ := by
    funext s
    rw [← hmul]
    congr 1
    ring
  change HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun s : ℝ => γ t * γ (s - t)) t _ at hh
  rw [heq] at hh
  apply hh.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  let s : ℝ := r
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) (s • v) =
    s • (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) v
  exact map_smul _ s v

theorem oneParameter_eq_groupExponential [T2Space G]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {γ : ℝ → G} (hzero : γ 0 = 1) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hd : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ 0
      ((ContinuousLinearMap.id ℝ ℝ).smulRight v)) :
    ∀ t, γ t = Exp (t • v) := by
  have hh := invariant_integralCurve_unique (oneParameter_isMIntegralCurve hzero hmul v hd)
    (hExp.isMIntegralCurve v) (by simpa only [zero_smul, hExp.map_zero] using hzero)
  exact congrFun hh

end PolycyclicRecognition

end

end OAI
