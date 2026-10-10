import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialProduct
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LocalParameterSmoothness
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialNaturality
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialTangentUniqueness

namespace OAI

/-! # Smoothness and differential of exponential-compatible homomorphisms

Coordinates of the second kind reduce smoothness to the individual
one-parameter subgroups. This applies to arbitrary finite-dimensional Lie
group targets and does not assume a linear representation of the target.
-/

noncomputable section
namespace PolycyclicRecognition

open Function
open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] [LieGroup (𝓘(ℝ, F)) ⊤ H] in
theorem map_exponentialProduct
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (φ : G →* H) (j : E →ₗ[ℝ] F)
    (hcompat : ∀ v, φ (ExpG v) = ExpH (j v))
    {n : ℕ} (v : Fin n → E) (x : Fin n → ℝ) :
    φ (exponentialProduct ExpG v x) =
      exponentialProduct ExpH (fun i => j (v i)) x := by
  induction n with
  | zero => exact φ.map_one
  | succ n ih =>
    simp only [exponentialProduct, map_mul]
    have hhead : φ (ExpG (x 0 • v 0)) = ExpH (x 0 • j (v 0)) :=
      (hcompat _).trans (congrArg ExpH (j.map_smul _ _))
    exact congrArg₂ (· * ·) hhead (ih (v ∘ Fin.succ) (x ∘ Fin.succ))

theorem contMDiffAt_one_of_exponential_compatibility [FiniteDimensional ℝ E]
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (hG : IsGroupExponential ExpG) (hH : IsGroupExponential ExpH)
    (φ : G →* H) (hφ : Continuous φ) (j : E →ₗ[ℝ] F)
    (hcompat : ∀ v, φ (ExpG v) = ExpH (j v)) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ φ 1 := by
  let b := Module.finBasis ℝ E
  let d := b.equivFun.toContinuousLinearEquiv.symm
  have hcomb : tangentCombination b = d.toContinuousLinearMap := by
    ext x
    simp only [tangentCombination_apply]
    exact (b.equivFun_symm_apply x).symm
  have hd : HasMFDerivAt (𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ)) (𝓘(ℝ, E))
      (exponentialProduct ExpG b) 0 d.toContinuousLinearMap := by
    apply (hG.hasMFDerivAt_exponentialProduct_zero b).congr_mfderiv
    exact hcomb
  have hp : ContMDiff (𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ)) (𝓘(ℝ, F)) ∞
      (φ ∘ exponentialProduct ExpG b) := by
    have heq : φ ∘ exponentialProduct ExpG b =
        exponentialProduct ExpH (fun i => j (b i)) := by
      funext x
      exact map_exponentialProduct φ j hcompat b x
    rw [heq]
    exact hH.contMDiff_exponentialProduct _
  have he : (φ ∘ exponentialProduct ExpG b) 0 = φ 1 := by
    simp only [Function.comp_apply, hG.exponentialProduct_zero]
  have hc : ContDiffAt ℝ ∞
      ((extChartAt (𝓘(ℝ, F)) (φ 1) ∘ φ) ∘ exponentialProduct ExpG b) 0 := by
    exact ((contMDiffAt_extChartAt (I := 𝓘(ℝ, F))).comp_of_eq hp.contMDiffAt he).contDiffAt
  have hh := contMDiffAt_of_local_parameterization
    (hG.contMDiff_exponentialProduct b).contMDiffAt hd hc
  apply contMDiffAt_iff_target.mpr
  refine ⟨hφ.continuousAt, ?_⟩
  simpa only [hG.exponentialProduct_zero] using hh

theorem contMDiff_of_exponential_compatibility [FiniteDimensional ℝ E]
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (hG : IsGroupExponential ExpG) (hH : IsGroupExponential ExpH)
    (φ : G →* H) (hφ : Continuous φ) (j : E →ₗ[ℝ] F)
    (hcompat : ∀ v, φ (ExpG v) = ExpH (j v)) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ φ := by
  have hbase := contMDiffAt_one_of_exponential_compatibility hG hH φ hφ j hcompat
  intro g
  have hl : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g⁻¹ * x) g :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := g⁻¹) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g⁻¹ * x)).contMDiffAt
  have hm := hbase.comp_of_eq hl (inv_mul_cancel g)
  have hh := (contMDiff_mul_left (I := 𝓘(ℝ, F)) (a := φ g) :
    ContMDiff (𝓘(ℝ, F)) (𝓘(ℝ, F)) ∞ (fun y : H => φ g * y)).contMDiffAt.comp g hm
  have heq : (fun x => φ g * φ (g⁻¹ * x)) = φ := by
    funext x
    rw [← map_mul, mul_inv_cancel_left]
  change ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ (fun x => φ g * φ (g⁻¹ * x)) g at hh
  rwa [heq] at hh

/-- Differentiating exponential compatibility recovers the specified linear map. -/
theorem mfderiv_eq_of_exponential_compatibility [T2Space H]
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (hG : IsGroupExponential ExpG) (hH : IsGroupExponential ExpH)
    (φ : G →* H) (hφ : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ)
    (j : E →ₗ[ℝ] F) (hcompat : ∀ v, φ (ExpG v) = ExpH (j v)) (v : E) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 v = j v := by
  apply hH.eq_of_oneParameter_eq
  intro t
  calc
    ExpH (t • mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 v) =
        ExpH (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 (t • v)) :=
      congrArg ExpH (map_smul (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 : E →L[ℝ] F) t v).symm
    _ = φ (ExpG (t • v)) := (hG.map_of_mdifferentiable hH φ hφ (t • v)).symm
    _ = ExpH (j (t • v)) := hcompat _
    _ = ExpH (t • j v) := by rw [map_smul]

end PolycyclicRecognition

end

end OAI
