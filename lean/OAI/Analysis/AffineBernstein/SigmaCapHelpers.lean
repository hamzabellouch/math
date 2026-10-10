import Mathlib
import OAI.Analysis.AffineBernstein.NewtonBasis
import OAI.Analysis.AffineBernstein.TiltedTrace

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section SigmaCapHelpers
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]

omit [CompleteSpace E] in
lemma tubeAngularDensity_reindex (H : S × E → ℝ) (q : S × E)
    (b : OrthonormalBasis ι ℝ E) (e : ι ≃ τ) :
    tubeAngularDensity H q (b.reindex e) = tubeAngularDensity H q b := by
  unfold tubeAngularDensity
  have hm : tubeFullRadiusMatrix H q (b.reindex e) =
      (tubeFullRadiusMatrix H q b).submatrix e.symm e.symm := by
    ext i j
    simp [tubeFullRadiusMatrix,OrthonormalBasis.reindex_apply]
  rw [hm,Matrix.adjugate_submatrix_equiv_self]
  exact e.symm.sum_comp (fun i => (tubeFullRadiusMatrix H q b).adjugate i i)

/-- The unnormalized support conormal has norm at least one at every unit normal.
This is independent of graph stationarity and uses the product norm literally. -/
lemma one_le_norm_supportConormal (H : S × E → ℝ) (s : S) {e : E} (he : ‖e‖ = 1) :
    1 ≤ ‖supportConormal H (s,e)‖ := by
  have hv : supportConormal H (s,e) (0,e) = -1 := by
    have hz : (fderiv ℝ H (s,e)) (0,0) = 0 := map_zero _
    simp [supportConormal,he,hz]
  have hn := (supportConormal H (s,e)).le_opNorm ((0:S),e)
  simpa [hv,Prod.norm_def,he] using hn

end SigmaCapHelpers

/-- The actual continuous linear forms chosen in bounds.tex256. -/
def capTiltedForm {k : ℕ} (j : Fin k) : Space k →L[ℝ] ℝ :=
  ∑ i, capTiltedCovector j i • EuclideanSpace.proj i
@[simp] lemma capTiltedForm_apply {k : ℕ} (j : Fin k) (s : Space k) :
    capTiltedForm j s = ∑ i, capTiltedCovector j i * s i := by
  simp [capTiltedForm, PiLp.proj_apply]
@[simp] lemma capTiltedForm_basis {k : ℕ} (j i : Fin k) :
    capTiltedForm j (EuclideanSpace.basisFun (Fin k) ℝ i) = capTiltedCovector j i := by
  simp [capTiltedForm_apply, EuclideanSpace.basisFun_apply]

end AffineBernstein
end

end OAI
