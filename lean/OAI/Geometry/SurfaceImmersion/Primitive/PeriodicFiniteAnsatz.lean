import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicFastEvaluation

namespace OAI

/-! The finite oscillatory map and its actual first derivatives. -/

noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def finiteAnsatz (F : A → E) (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ)
    (L : ℕ) (z : ℝ) (p : A) : E :=
  F p + ∑ i ∈ Finset.range L, z ^ (i + 1) • (U i).fastValue ℓ z p

lemma finiteAnsatz_smooth {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    ContDiff ℝ ∞ (finiteAnsatz F U ℓ L z) :=
  hF.add (ContDiff.sum fun i _ => contDiff_const.smul ((U i).fastValue_smooth ℓ z))

lemma finiteAnsatz_fderiv {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) (p v : A) :
    fderiv ℝ (finiteAnsatz F U ℓ L z) p v = fderiv ℝ F p v +
      ∑ i ∈ Finset.range L, z ^ (i + 1) •
        (((U i).slow v).val p ((ℓ p / z : ℝ) : Period) +
          (ℓ v / z) • (U i).angle.val p ((ℓ p / z : ℝ) : Period)) := by
  have hd (i : ℕ) : DifferentiableAt ℝ ((U i).fastValue ℓ z) p :=
    ((U i).fastValue_smooth ℓ z).differentiable (by simp) p
  have hterm (i : ℕ) : DifferentiableAt ℝ
      (fun q => z ^ (i + 1) • (U i).fastValue ℓ z q) p := (hd i).const_smul _
  have hsum : DifferentiableAt ℝ
      (fun q => ∑ i ∈ Finset.range L, z ^ (i + 1) • (U i).fastValue ℓ z q) p :=
    DifferentiableAt.fun_sum (fun i _ => hterm i)
  unfold finiteAnsatz
  rw [fderiv_fun_add (hF.differentiable (by simp) p) hsum]
  rw [fderiv_fun_sum (fun i _ => hterm i)]
  simp only [add_apply, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [fderiv_fun_const_smul (hd i), smul_apply,
    Family.fastValue_fderiv]

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
