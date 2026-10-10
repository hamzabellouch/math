import Mathlib
import OAI.Analysis.AffineBernstein.AngularCalculus
import OAI.Analysis.AffineBernstein.CofactorCodazzi

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem third_derivative_swap_last {H : E → ℝ} {e : E}
    (hh : ContDiffAt ℝ ∞ H e) (u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ H)) e u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ H)) e u w v := by
  have hd := ((hh.fderiv_right (m := ∞) (by simp)).fderiv_right
    (m := ∞) (by simp)).differentiableAt (by simp)
  have he : (fun y => fderiv ℝ (fderiv ℝ H) y v w) =ᶠ[𝓝 e]
      (fun y => fderiv ℝ (fderiv ℝ H) y w v) := by
    filter_upwards [(hh.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually
      (by simp)] with q hq
    exact (hq.isSymmSndFDerivAt (by norm_num)).eq v w
  have hdv := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v e)).clm_apply
    (hasFDerivAt_const w e)
  have hdw := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w e)).clm_apply
    (hasFDerivAt_const v e)
  have heq := (hdv.congr_of_eventuallyEq he.symm).unique hdw
  have hev := congrArg (fun L : E →L[ℝ] ℝ => L u) heq
  simpa using hev

/- Radius matrix in projected constant tangent frames. At a unit `e` and an
orthonormal tangent frame this is exactly `∇²_S h + h Id`; its first derivatives
are the round covariant derivatives in a normal frame. -/
def radiusMatrix {ι : Type*} (H : E → ℝ) (frame : ι → E) (e : E) : Matrix ι ι ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ H) e
    (tangentProjection e (frame i)) (tangentProjection e (frame j))

theorem radiusMatrix_eq {ι : Type*} {H : E → ℝ} {e : E}
    (hh : ContDiffAt ℝ ∞ H e) (frame : ι → E)
    (hf : ∀ i, inner ℝ e (frame i) = 0) (i j : ι) :
    radiusMatrix H frame e i j = sphereRadius H e (frame i) (frame j) := by
  rw [sphereRadius_eq_hessian hh _ _ (hf j)]
  simp [radiusMatrix, tangentProjection_eq (hf i), tangentProjection_eq (hf j)]

/- The angular cofactor divergence identity, derived from the actual Hessian
and Euler radial identity, not assumed as a stationarity hypothesis. -/
theorem radiusMatrix_cofactor_divergence {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : E → ℝ} {e : E} (hh : ContDiffAt ℝ ∞ H e)
    (hrad : ∀ v, fderiv ℝ (fderiv ℝ H) e v e = 0)
    (frame : ι → E) (hf : ∀ i, inner ℝ e (frame i) = 0) (i : ι) :
    (∑ j, fderiv ℝ (fun y => (radiusMatrix H frame y).adjugate j i) e (frame j)) = 0 := by
  have hd := ((hh.fderiv_right (m := ∞) (by simp)).fderiv_right
    (m := ∞) (by simp)).differentiableAt (by simp)
  have hrad' (q : E) : fderiv ℝ (fderiv ℝ H) e e q = 0 ∧
      fderiv ℝ (fderiv ℝ H) e q e = 0 := by
    refine ⟨?_, hrad q⟩
    rw [(hh.isSymmSndFDerivAt (by simp)).eq e q]
    exact hrad q
  apply cofactor_divergence_of_codazzi (radiusMatrix H frame) e frame
  · intro l m
    exact ((hd.hasFDerivAt.clm_apply (hasFDerivAt_tangentProjection e (frame l))).clm_apply
      (hasFDerivAt_tangentProjection e (frame m))).differentiableAt
  · intro l j m
    change roundTensorDerivative (fderiv ℝ (fderiv ℝ H)) e (frame j) (frame l) (frame m) =
      roundTensorDerivative (fderiv ℝ (fderiv ℝ H)) e (frame m) (frame l) (frame j)
    rw [roundTensorDerivative_eq hd hrad' _ _ _ (hf l) (hf m),
      roundTensorDerivative_eq hd hrad' _ _ _ (hf l) (hf j)]
    have hs := (hh.fderiv_right (m := ∞) (by simp)).isSymmSndFDerivAt (by simp)
    calc
      _ = fderiv ℝ (fderiv ℝ (fderiv ℝ H)) e (frame l) (frame j) (frame m) :=
        congrArg (fun L : E →L[ℝ] ℝ => L (frame m)) (hs.eq (frame j) (frame l))
      _ = fderiv ℝ (fderiv ℝ (fderiv ℝ H)) e (frame l) (frame m) (frame j) :=
        third_derivative_swap_last hh _ _ _
      _ = _ := congrArg (fun L : E →L[ℝ] ℝ => L (frame j)) (hs.eq (frame l) (frame m))

end AffineBernstein
end

end OAI
