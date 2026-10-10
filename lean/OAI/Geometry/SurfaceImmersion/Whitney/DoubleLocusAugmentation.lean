import OAI.Geometry.SurfaceImmersion.Whitney.QuadraticDoubleTransverse
import Mathlib.LinearAlgebra.Projection

namespace OAI

/-! A three-dimensional submersion on the four-dimensional pair chart
admits one additional linear coordinate with invertible derivative. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem double_locus_linear_augmentation (K : (Base × Base) →L[ℝ] ProjectionTarget 3)
    (hK : Function.Surjective K) :
    ∃ ℓ : (Base × Base) →L[ℝ] ℝ, Function.Bijective (K.prod ℓ) := by
  have hdim : Module.finrank ℝ K.ker = 1 := by
    have h := K.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hK,finrank_top] at h
    have hE : Module.finrank ℝ (Base × Base) = 4 := by simp [Base]
    have hF : Module.finrank ℝ (ProjectionTarget 3) = 3 := by simp [ProjectionTarget]
    rw [hE,hF] at h
    omega
  let e : K.ker ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  obtain ⟨P,hP⟩ := K.ker.exists_isCompl
  let π : (Base × Base) →L[ℝ] K.ker := (K.ker.projectionOnto P hP).toContinuousLinearMap
  let ℓ : (Base × Base) →L[ℝ] ℝ := e.toContinuousLinearMap.comp π
  have hzero (x : Base × Base) (hx : K x = 0) (hℓ : ℓ x = 0) : x = 0 := by
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
  simp [Base,ProjectionTarget]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
