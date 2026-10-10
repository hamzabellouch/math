import OAI.Geometry.Relativity.CKS.SchwarzschildHorizonExclusionDefinitions

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma first_basis_ne_zero : (EuclideanSpace.single 0 1 : E2) ≠ 0 := by
  intro hh
  have := congrArg (fun x : E2 => x 0) hh
  simp at this
lemma secondResidual_ne_zero (g : E3 →L[ℝ] E3 →L[ℝ] ℝ) (T : E2 →L[ℝ] E3) :
    secondResidual g T ≠ 0 := by
  intro hh
  have := congrArg (fun x : E2 => x 1) hh
  simp [secondResidual] at this

lemma normalized_metric_unit (g : E3 →L[ℝ] E3 →L[ℝ] ℝ) (v : E3)
    (hv : 0 < g v v) :
    g ((Real.sqrt (g v v))⁻¹ • v) ((Real.sqrt (g v v))⁻¹ • v) = 1 := by
  have hp := Real.sqrt_pos.mpr hv
  have hs := Real.sq_sqrt hv.le
  simp only [map_smul,smul_apply,smul_eq_mul]
  field_simp
  nlinarith

lemma firstFrame_unit (g : E3 →L[ℝ] E3 →L[ℝ] ℝ) (T : E2 →L[ℝ] E3)
    (hg : ∀ v, v ≠ 0 → 0 < g v v) (hT : Function.Injective T) :
    g (T (firstFrame g T)) (T (firstFrame g T)) = 1 := by
  have hne : T (EuclideanSpace.single 0 1) ≠ 0 := by
    simpa only [map_zero] using hT.ne first_basis_ne_zero
  simpa only [firstFrame,map_smul] using normalized_metric_unit g _ (hg _ hne)

lemma secondFrame_unit (g : E3 →L[ℝ] E3 →L[ℝ] ℝ) (T : E2 →L[ℝ] E3)
    (hg : ∀ v, v ≠ 0 → 0 < g v v) (hT : Function.Injective T) :
    g (T (secondFrame g T)) (T (secondFrame g T)) = 1 := by
  have hne : T (secondResidual g T) ≠ 0 := by
    simpa only [map_zero] using hT.ne (secondResidual_ne_zero g T)
  simpa only [secondFrame,map_smul] using normalized_metric_unit g _ (hg _ hne)

lemma frames_orthogonal (g : E3 →L[ℝ] E3 →L[ℝ] ℝ) (T : E2 →L[ℝ] E3)
    (hg : ∀ v, v ≠ 0 → 0 < g v v) (hT : Function.Injective T) :
    g (T (firstFrame g T)) (T (secondFrame g T)) = 0 := by
  have hne : T (EuclideanSpace.single 0 1) ≠ 0 := by
    simpa only [map_zero] using hT.ne first_basis_ne_zero
  have hpos := hg _ hne
  have hr : g (T (EuclideanSpace.single 0 1)) (T (secondResidual g T)) = 0 := by
    simp only [secondResidual,map_sub,map_smul,smul_eq_mul]
    field_simp
    ring
  simp only [firstFrame,secondFrame,map_smul,smul_apply,smul_eq_mul]
  rw [hr,mul_zero,mul_zero]

end CKSSchwarzschild

end

end OAI
