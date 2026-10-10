import OAI.Geometry.Relativity.CKS.SchwarzschildCoordinates
import OAI.Geometry.Relativity.CKS.InducedMetric

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

def coneLinear (r : ℝ) (n : E3) (A : E2 →L[ℝ] E3) : E3 →L[ℝ] E3 :=
  firstCoordinate.smulRight n + r • A.comp dropPlane
@[simp] lemma coneLinear_apply (r : ℝ) (n : E3) (A : E2 →L[ℝ] E3) (v : E3) :
    coneLinear r n A v = (v 0) • n + r • A (dropPlane v) := rfl

lemma coneLinear_basis_zero (r : ℝ) (n : E3) (A : E2 →L[ℝ] E3) :
    coneLinear r n A (EuclideanSpace.basisFun (Fin 3) ℝ 0) = n := by
  have hd : dropPlane (EuclideanSpace.basisFun (Fin 3) ℝ 0) = 0 := by
    ext index; simp
  rw [coneLinear_apply,hd,map_zero A,smul_zero,add_zero]
  have h0 : (EuclideanSpace.basisFun (Fin 3) ℝ 0) 0 = 1 := by simp
  rw [h0,one_smul]
lemma coneLinear_basis_succ (r : ℝ) (n : E3) (A : E2 →L[ℝ] E3) (i : Fin 2) :
    coneLinear r n A (EuclideanSpace.basisFun (Fin 3) ℝ i.succ) =
      r • A (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  rw [coneLinear_apply]
  have h0 : (EuclideanSpace.basisFun (Fin 3) ℝ i.succ) 0 = 0 := by simp
  have hd : dropPlane (EuclideanSpace.basisFun (Fin 3) ℝ i.succ) =
      EuclideanSpace.basisFun (Fin 2) ℝ i := by
    ext j
    simp [EuclideanSpace.basisFun_apply,EuclideanSpace.single]
  rw [h0,hd,zero_smul,zero_add]

lemma abs_det_coneLinear (r : ℝ) (n : E3) (A : E2 →L[ℝ] E3)
    (hn : ‖n‖ = 1) (hA : ∀ v, ⟪n,A v⟫_ℝ = 0) :
    |(coneLinear r n A).det| = r^2 * Real.sqrt
      (Matrix.gram ℝ (fun i : Fin 2 => A (EuclideanSpace.basisFun (Fin 2) ℝ i))).det := by
  let B := EuclideanSpace.basisFun (Fin 3) ℝ
  let C := EuclideanSpace.basisFun (Fin 2) ℝ
  have hnorm := (coneLinear r n A).toLinearMap.normDet_sq_eq_det_gram B
  rw [LinearMap.normDet_eq_norm_det,Real.norm_eq_abs] at hnorm
  have hGram : (Matrix.gram ℝ (fun i : Fin 3 => coneLinear r n A (B i))).det =
      r^4 * (Matrix.gram ℝ (fun i : Fin 2 => A (C i))).det := by
    have hAn : ∀ v, ⟪A v,n⟫_ℝ = 0 := fun v => (real_inner_comm _ _).trans (hA v)
    simp only [Matrix.det_fin_three,Matrix.det_fin_two,Matrix.gram_apply,B,C]
    simp only [show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
      show (2 : Fin 3) = (1 : Fin 2).succ from rfl,
      coneLinear_basis_zero,coneLinear_basis_succ,inner_smul_left,inner_smul_right,
      starRingEnd_apply,star_trivial,hA,hAn,real_inner_self_eq_norm_sq,hn]
    ring
  change |(coneLinear r n A).det| ^ 2 =
    (Matrix.gram ℝ (fun i : Fin 3 => coneLinear r n A (B i))).det at hnorm
  rw [hGram] at hnorm
  have hnn : 0 ≤ (Matrix.gram ℝ (fun i : Fin 2 => A (C i))).det :=
    (Matrix.posSemidef_gram ℝ _).det_nonneg
  have hs := Real.sq_sqrt hnn
  have hpos : 0 ≤ r^2 * Real.sqrt (Matrix.gram ℝ (fun i : Fin 2 => A (C i))).det := by positivity
  apply (sq_eq_sq₀ (abs_nonneg _) hpos).mp
  rw [mul_pow,Real.sq_sqrt hnn,← pow_mul]
  exact hnorm

end CKSSchwarzschild

end

end OAI
