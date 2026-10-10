import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFiniteRankCriterion
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Operator.Bilinear

namespace OAI

/-! # Holomorphic finite-dimensional obstruction for the linearized step

The Schur determinant is holomorphic on the resolvent of the contracting
part. This is the scalar analytic function used to isolate the remaining
spectral points of the actual finite-rank decomposition.
-/

namespace DefocusingNLS

private theorem matrix_det_analyticAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℂ → Matrix ι ι ℂ) (z : ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun w => M w i j) z) :
    AnalyticAt ℂ (fun w => (M w).det) z := by
  simp_rw [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  exact hM (σ i) i

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

local instance : CompleteSpace F := FiniteDimensional.complete ℂ F

theorem finiteDimensional_det_analyticAt (D : ℂ → F →L[ℂ] F) (z : ℂ)
    (hD : AnalyticAt ℂ D z) : AnalyticAt ℂ (fun w => (D w).det) z := by
  let b := Module.finBasis ℂ F
  have hentry (i j : Fin (Module.finrank ℂ F)) :
      AnalyticAt ℂ (fun w => LinearMap.toMatrix b b (D w).toLinearMap i j) z := by
    let L := ((b.coord i).toContinuousLinearMap).comp
      (ContinuousLinearMap.apply ℂ F (b j))
    simpa only [Function.comp_def, L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, LinearMap.toMatrix_apply]
      using! (L.analyticAt (D z)).comp hD
  have h := matrix_det_analyticAt
    (fun w => LinearMap.toMatrix b b (D w).toLinearMap) z hentry
  simpa only [LinearMap.det_toMatrix] using h

theorem operator_resolvent_analyticAt (B : E →L[ℂ] E) (z : ℂ)
    (hz : z ∈ resolventSet ℂ B) : AnalyticAt ℂ (resolvent B) z := by
  let A := fun w : ℂ => w • (1 : E →L[ℂ] E) - B
  have hA : AnalyticAt ℂ A z :=
    ((analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) z).smul
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : E →L[ℂ] E)) z)).sub
        analyticAt_const
  have hunit : IsUnit (A z) := by
    have hu : IsUnit (algebraMap ℂ (E →L[ℂ] E) z - B) := hz
    simpa only [A, Algebra.algebraMap_eq_smul_one] using hu
  have hi : AnalyticAt ℂ Ring.inverse (A z) := by
    convert! (analyticAt_inverse (𝕜 := ℂ) hunit.unit) using 1
  convert! hi.comp hA using 1

theorem finiteRank_determinant_analyticAt (B : E →L[ℂ] E) (U : F →L[ℂ] E)
    (V : E →L[ℂ] F) (z : ℂ) (hz : z ∈ resolventSet ℂ B) :
    AnalyticAt ℂ (fun w =>
      (ContinuousLinearMap.id ℂ F - V.comp ((resolvent B w).comp U)).det) z := by
  let K : (E →L[ℂ] E) →L[ℂ] (F →L[ℂ] F) :=
    (ContinuousLinearMap.compL ℂ F E F V).comp
      ((ContinuousLinearMap.compL ℂ F E E).flip U)
  have hR := operator_resolvent_analyticAt B z hz
  have hK := (K.analyticAt (resolvent B z)).comp hR
  exact finiteDimensional_det_analyticAt _ z (analyticAt_const.sub hK)

end

end DefocusingNLS

end OAI
