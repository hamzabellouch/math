import OAI.Geometry.SurfaceImmersion.Whitney.QuadraticDoubleTransverse
import Mathlib.LinearAlgebra.Projection

namespace OAI

/-! A surjective linear map with a one-dimensional kernel admits one
additional linear coordinate with invertible derivative. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem one_fiber_linear_augmentation (hdimEF : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (K : E →L[ℝ] F)
    (hK : Function.Surjective K) :
    ∃ ℓ : E →L[ℝ] ℝ, Function.Bijective (K.prod ℓ) := by
  have hdim : Module.finrank ℝ K.ker = 1 := by
    have h := K.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hK,finrank_top] at h
    omega
  let e : K.ker ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  obtain ⟨P,hP⟩ := K.ker.exists_isCompl
  let π : E →L[ℝ] K.ker := (K.ker.projectionOnto P hP).toContinuousLinearMap
  let ℓ : E →L[ℝ] ℝ := e.toContinuousLinearMap.comp π
  have hzero (x : E) (hx : K x = 0) (hℓ : ℓ x = 0) : x = 0 := by
    have hmem : x ∈ K.ker := hx
    have hπ : π x = ⟨x,hmem⟩ := by
      exact Submodule.projectionOnto_apply_of_mem_left hP hmem
    have he : e (⟨x,hmem⟩ : K.ker) = e 0 := by
      simpa only [ℓ,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,hπ,map_zero] using hℓ
    exact congrArg Subtype.val (e.injective he)
  have hi : Function.Injective (K.prod ℓ) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    · rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.fst hxy)
    · rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.snd hxy)
  refine ⟨ℓ,hi,?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (K.prod ℓ).toLinearMap) _).mp hi
  simpa using hdimEF

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
