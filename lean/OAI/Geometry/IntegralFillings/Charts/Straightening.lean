import Mathlib
import OAI.Geometry.IntegralFillings.Model

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace EuclideanStraightening
variable {d : ℕ}
noncomputable def replaceMap (j : Fin d) (g : Euc d → ℝ) (z : Euc d) : Euc d :=
  z + (g z-z j) • EuclideanSpace.single j 1

@[simp] lemma replaceMap_apply (j : Fin d) (g : Euc d → ℝ) (z : Euc d) (i : Fin d) :
    replaceMap j g z i = if i=j then g z else z i := by
  simp only [replaceMap,PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,
    smul_eq_mul,mul_ite,mul_one,mul_zero]
  split_ifs with hi
  · subst i; ring
  · ring

lemma replaceMap_lipschitz (j : Fin d) {g : Euc d → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    LipschitzWith (1+K+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊) (replaceMap j g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h1 := hg.dist_le_mul x y
  have h2 := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).lipschitzWith.dist_le_mul x y
  have h3 : ‖(g x-x j)-(g y-y j)‖ ≤ ((K:ℝ)+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊)*‖x-y‖ := by
    have htriangle : ‖(g x-x j)-(g y-y j)‖ ≤ ‖g x-g y‖+‖x j-y j‖ := by
      convert norm_sub_le (g x-g y) (x j-y j) using 1
      congr 1
      ring
    simp only [dist_eq_norm] at h1 h2
    change ‖x j-y j‖ ≤ _ at h2
    nlinarith
  simp only [replaceMap,dist_eq_norm]
  have he : x+(g x-x j) • EuclideanSpace.single j 1-
      (y+(g y-y j) • EuclideanSpace.single j 1) =
      (x-y)+((g x-x j)-(g y-y j)) • EuclideanSpace.single j 1 := by
    module
  rw [he]
  calc
    _ ≤ ‖x-y‖ + ‖((g x-x j)-(g y-y j)) • EuclideanSpace.single j 1‖ := norm_add_le _ _
    _ = ‖x-y‖+‖(g x-x j)-(g y-y j)‖ := by simp [norm_smul]
    _ ≤ ‖x-y‖+(((K:ℝ)+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊)*‖x-y‖) := add_le_add_right h3 ‖x-y‖
    _ = _ := by simp only [NNReal.coe_add,NNReal.coe_one]; ring

lemma det_updateRow_one (j : Fin d) (v : Fin d → ℝ) :
    (Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j v).det = v j := by
  have he : (∑ i : Fin d, v i • (1 : Matrix (Fin d) (Fin d) ℝ) i) = v := by
    ext l
    simp [Matrix.one_apply]
  rw [←he,Matrix.det_updateRow_sum]
  simp [Matrix.one_apply]

lemma replaceMap_hasFDerivAt {g : Euc d → ℝ} {x : Euc d} (hg : DifferentiableAt ℝ g x)
    (j : Fin d) : HasFDerivAt (replaceMap j g)
      (ContinuousLinearMap.id ℝ (Euc d)+(fderiv ℝ g x-EuclideanSpace.proj j).smulRight
        (EuclideanSpace.single j 1)) x :=
  (hasFDerivAt_id x).add ((hg.hasFDerivAt.sub (EuclideanSpace.proj j).hasFDerivAt).smul_const _)

lemma det_replaceMap_fderiv {g : Euc d → ℝ} {x : Euc d} (hg : DifferentiableAt ℝ g x)
    (j : Fin d) :
    (Matrix.of fun i l : Fin d => fderiv ℝ (replaceMap j g) x (EuclideanSpace.single l 1) i).det =
      fderiv ℝ g x (EuclideanSpace.single j 1) := by
  rw [(replaceMap_hasFDerivAt hg j).fderiv]
  have he : (Matrix.of fun i l : Fin d =>
      (ContinuousLinearMap.id ℝ (Euc d)+(fderiv ℝ g x-EuclideanSpace.proj j).smulRight
        (EuclideanSpace.single j 1)) (EuclideanSpace.single l 1) i) =
      Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j
        (fun l => fderiv ℝ g x (EuclideanSpace.single l 1)) := by
    ext i l
    by_cases hi : i=j
    · subst i
      simp [ContinuousLinearMap.smulRight_apply,PiLp.single_apply,
        Matrix.updateRow,Function.update]
    · simp [ContinuousLinearMap.smulRight_apply,PiLp.single_apply,
        Matrix.updateRow,Function.update,Matrix.one_apply,hi]
  rw [he,det_updateRow_one]

noncomputable def switchZero {k : ℕ} (j : Fin (k+1)) : Euc (k+1) ≃ₗᵢ[ℝ] Euc (k+1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 j)

@[simp] lemma switchZero_apply_zero {k : ℕ} (j : Fin (k+1)) (z : Euc (k+1)) :
    switchZero j z 0 = z j := by
  simp [switchZero,Equiv.piCongrLeft']

noncomputable def straightenMap {k : ℕ} (j : Fin (k+1)) (g : Euc (k+1) → ℝ) :
    Euc (k+1) → Euc (k+1) := switchZero j ∘ replaceMap j g

@[simp] lemma straightenMap_zero {k : ℕ} (j : Fin (k+1)) (g : Euc (k+1) → ℝ) (z : Euc (k+1)) :
    straightenMap j g z 0 = g z := by simp [straightenMap]

lemma straightenMap_lipschitz {k : ℕ} (j : Fin (k+1)) {g : Euc (k+1) → ℝ}
    {K : ℝ≥0} (hg : LipschitzWith K g) :
    LipschitzWith (1+K+‖(EuclideanSpace.proj j : Euc (k+1) →L[ℝ] ℝ)‖₊) (straightenMap j g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (switchZero j (replaceMap j g x)) (switchZero j (replaceMap j g y)) ≤ _
  rw [(switchZero j).isometry.dist_eq]
  exact (replaceMap_lipschitz j hg).dist_le_mul x y

end EuclideanStraightening
end SharpIntegralFillings

end

end OAI
