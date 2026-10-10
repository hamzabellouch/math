import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieExponential
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

namespace OAI

/-! # Intrinsic exponential curves and the invariant vector field

The group law and derivative at zero determine the global differential
equation of an intrinsic exponential curve.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

omit [FiniteDimensional ℝ E] in
theorem IsGroupExponential.isMIntegralCurve
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) (fun t : ℝ => Exp (t • v))
      (mulInvariantVectorField v) := by
  intro t
  let γ : ℝ → G := fun s => Exp (s • v)
  let D : ℝ →L[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v
  have hzero : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (t - t) D := by
    rw [sub_self]
    exact hExp.hasMFDerivAt_zero v
  have hshift : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun s : ℝ => s - t) t
      (ContinuousLinearMap.id ℝ ℝ) := by
    have hD : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) =
        ContinuousLinearMap.id ℝ ℝ := by ext; simp
    simpa only [id_eq, hD] using
      ((hasDerivAt_id t).sub_const t).hasFDerivAt.hasMFDerivAt
  have hbase := HasMFDerivAt.comp t (f := fun s : ℝ => s - t) hzero hshift
  have hleft : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g)
      (γ (t - t)) (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) := by
    rw [show γ (t - t) = 1 from by simp [γ, hExp.map_zero]]
    have h : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1 :=
      (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := γ t) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun g : G => γ t * g)).mdifferentiableAt
        (by simp)
    exact h.hasMFDerivAt
  have hder := hleft.comp t hbase
  have heq : (fun s : ℝ => γ t * γ (s - t)) = γ := by
    funext s
    dsimp [γ]
    rw [← hExp.map_add_smul]
    congr 2
    ring
  change HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ t _
  change HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E))
    (fun s : ℝ => γ t * γ (s - t)) t _ at hder
  rw [heq] at hder
  apply hder.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  let s : ℝ := r
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) (s • v) =
    s • (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) v
  exact map_smul _ s v

omit [FiniteDimensional ℝ E] in
/-- The intrinsic characterization determines the exponential uniquely.
This uses manifold ODE uniqueness for the already constructed invariant
vector field, with no external Lie-theoretic input. -/
theorem IsGroupExponential.unique [T2Space G]
    {Exp Exp' : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    (hExp : IsGroupExponential Exp) (hExp' : IsGroupExponential Exp') : Exp = Exp' := by
  funext v
  have hv : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) 1
      (fun g : G => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle (𝓘(ℝ, E)) G)) :=
    (contMDiff_mulInvariantVectorField v).of_le (by norm_num)
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv
    (hExp.isMIntegralCurve v) (hExp'.isMIntegralCurve v)
    (by simp only [zero_smul, hExp.map_zero, hExp'.map_zero])
  simpa only [one_smul] using congrFun heq 1

end PolycyclicRecognition

end

end OAI
