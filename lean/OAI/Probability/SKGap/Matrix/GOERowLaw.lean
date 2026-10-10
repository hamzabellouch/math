import Mathlib
import OAI.Probability.SKGap.Gaussian.GOEGaussian

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
lemma goe_row_gaussian (r : ℝ) (i : ι) (e : κ→ι) :
    HasGaussianLaw (fun g : MatrixCoordinates ι→ℝ=>fun k=>goeMatrix r g i (e k))
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  exact (goe_matrix_gaussian r).map_fun
    (ContinuousLinearMap.pi (fun k=>ContinuousLinearMap.proj (i,e k)) :
      ((ι × ι)→ℝ) →L[ℝ] (κ→ℝ))

omit [Fintype κ] in
lemma goe_row_cov {r : ℝ} (hr : 0 ≤ r) (i : ι) (e : κ ↪ ι)
    (he : ∀ k,e k≠i) (k l : κ) :
    cov[fun g=>goeMatrix r g i (e k),fun g=>goeMatrix r g i (e l);
      gaussianCoordinates (MatrixCoordinates ι)]=if k=l then r else 0 := by
  classical
  rw [goe_entry_cov hr]
  have hi : ∀ k,¬i=e k := fun k=>Ne.symm (he k)
  simp only [ite_true,hi,he,e.injective.eq_iff]
  simp only [ite_false,mul_zero,add_zero]
  split_ifs <;> simp_all

lemma goe_row_hasLaw {r : ℝ} (hr : 0 ≤ r) (i : ι) (e : κ ↪ ι)
    (he : ∀ k,e k≠i) :
    HasLaw (fun g : MatrixCoordinates ι→ℝ=>fun k=>goeMatrix r g i (e k))
      (Measure.pi (fun _ : κ=>gaussianReal 0 (Real.toNNReal r)))
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  classical
  have hg := goe_row_gaussian r i e
  have hl (k : κ) : HasLaw (fun g=>goeMatrix r g i (e k))
      (gaussianReal 0 (Real.toNNReal r)) (gaussianCoordinates (MatrixCoordinates ι)) := by
    refine ⟨(hg.eval k).aemeasurable,?_⟩
    rw [(hg.eval k).map_eq_gaussianReal,goe_mean_zero,
      ← covariance_self (hg.eval k).aemeasurable,goe_row_cov hr i e he,ite_eq_left rfl]
  exact iIndepFun.hasLaw_pi hl (hg.iIndepFun_of_covariance_eq_zero
    (fun k l h=>by rw [goe_row_cov hr i e he,ite_eq_right h]))
end SKGap

end
end

end OAI
