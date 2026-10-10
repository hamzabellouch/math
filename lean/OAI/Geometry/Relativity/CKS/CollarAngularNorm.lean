import OAI.Geometry.Relativity.CKS.ConeSupport

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise InnerProductSpace

abbrev AngularEuclidean := EuclideanSpace ℝ I

def covectorEmbedding (q : Mat) (E : I → ℝ) : AngularEuclidean :=
  WithLp.toLp 2 ![Real.sqrt (q 1 1/determinant q)*(E 0-q 0 1/q 1 1*E 1),
    E 1/Real.sqrt (q 1 1)]

def positiveAngular (q : Mat) : Prop := 0 < q 1 1 ∧ 0 < determinant q

lemma covectorEmbedding_smooth {q : Mat} {E : I → ℝ} (hq : positiveAngular q) :
    ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => covectorEmbedding p.1 p.2) (q,E) := by
  apply ((WithLp.linearEquiv 2 ℝ (I → ℝ)).symm.toContinuousLinearEquiv).contDiff.contDiffAt.comp (q,E)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) =>
      Real.sqrt (p.1 1 1/determinant p.1)*(p.2 0-p.1 0 1/p.1 1 1*p.2 1)) (q,E)
    apply ContDiffAt.mul
    · exact ((by fun_prop : ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.1 1 1) (q,E)).div
        (determinant_smooth.contDiffAt.comp (q,E) (by fun_prop : ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.1) (q,E))) hq.2.ne').sqrt
          (div_pos hq.1 hq.2).ne'
    · apply (by fun_prop : ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.2 0) (q,E)).sub
      exact ((by fun_prop : ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.1 0 1) (q,E)).div
        (by fun_prop) hq.1.ne').mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.2 1/Real.sqrt (p.1 1 1)) (q,E)
    exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.2 1) (q,E)).div
      ((by fun_prop : ContDiffAt ℝ ∞ (fun p : Mat × (I → ℝ) => p.1 1 1) (q,E)).sqrt hq.1.ne')
      (Real.sqrt_pos.mpr hq.1).ne'

lemma covectorEmbedding_linear (q : Mat) (c : ℝ) (E : I → ℝ) :
    covectorEmbedding q (c • E) = c • covectorEmbedding q E := by
  ext i
  fin_cases i <;> simp [covectorEmbedding] <;> ring

lemma covectorEmbedding_norm_sq {q : Mat} (hq : positiveAngular q) (hs : q 1 0=q 0 1)
    (E : I → ℝ) : ‖covectorEmbedding q E‖^2 = ∑ i, ∑ k, inverse q i k*E i*E k := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [covectorEmbedding,Fin.sum_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,Real.norm_eq_abs,sq_abs]
  have hsqrt : Real.sqrt (q 1 1/determinant q)^2 = q 1 1/determinant q :=
    Real.sq_sqrt (div_pos hq.1 hq.2).le
  have hsqrt' : Real.sqrt (q 1 1)^2 = q 1 1 := Real.sq_sqrt hq.1.le
  rw [mul_pow,div_pow,hsqrt,hsqrt']
  simp only [inverse,hs]
  have hd : determinant q=q 0 0*q 1 1-q 0 1*q 0 1 := by simp [determinant,hs]
  field_simp [hq.1.ne',hq.2.ne']
  rw [hd]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma covectorEmbedding_norm {q : Mat} (hq : positiveAngular q) (hs : q 1 0=q 0 1)
    (E : I → ℝ) : ‖covectorEmbedding q E‖ = Real.sqrt (∑ i, ∑ k, inverse q i k*E i*E k) := by
  rw [← covectorEmbedding_norm_sq hq hs,Real.sqrt_sq (norm_nonneg _)]

end
end CKSAngularGeometry

end

end OAI
