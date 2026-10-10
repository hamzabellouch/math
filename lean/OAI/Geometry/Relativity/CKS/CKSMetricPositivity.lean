import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.CKSPhysicalCoefficients

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def metricBlock (a : ℝ) (b : Point) (q : Mat) : AmbientMat :=
  !![a,b 0,b 1;b 0,q 0 0,q 0 1;b 1,q 1 0,q 1 1]

def cksMetric (r : ℝ) (f : MassFields) (x : Point) : AmbientMat :=
  metricBlock (cksRadialMetric r f x) (f.b x) (cksGamma r f x)

lemma metricBlock_submatrix (a : ℝ) (b : Point) (q : Mat) :
    (metricBlock a b q).submatrix Fin.succ Fin.succ = q := by
  ext i k
  fin_cases i <;> fin_cases k <;> rfl

lemma metricBlock_leaf_posDef {a : ℝ} {b : Point} {q : Mat} (h : (metricBlock a b q).PosDef) :
    q.PosDef := by
  have hi : Function.Injective (Fin.succ : I → Fin 3) := Fin.succ_injective 2
  simpa only [metricBlock_submatrix] using h.submatrix hi

lemma inverse_quadratic (q : Mat) (hq : determinant q ≠ 0) (b : Point) :
    (∑ i, ∑ k, q i k*(∑ a, inverse q i a*b a)*(∑ a, inverse q k a*b a)) =
      ∑ i, ∑ k, inverse q i k*(b i*b k) := by
  simp only [Fin.sum_univ_two,inverse]
  field_simp
  dsimp [determinant] at *
  ring

lemma inverse_mul_vector (q : Mat) (hq : determinant q ≠ 0) (b : Point) (i : I) :
    ∑ k, q i k*(∑ a, inverse q k a*b a) = b i := by
  fin_cases i <;> simp only [Fin.sum_univ_two,inverse] <;>
    field_simp <;> dsimp [determinant] at * <;> ring

lemma metricBlock_schur_positive {a : ℝ} {b : Point} {q : Mat}
    (h : (metricBlock a b q).PosDef) :
    0 < a-∑ i, ∑ k, inverse q i k*(b i*b k) := by
  have hq : determinant q ≠ 0 := by rw [determinant_eq]; exact (metricBlock_leaf_posDef h).det_pos.ne'
  let s : Point := fun i => ∑ k, inverse q i k*b k
  let v : Fin 3 → ℝ := ![1,-s 0,-s 1]
  have hv : v ≠ 0 := by
    intro hh
    have hh' := congrFun hh 0
    norm_num [v] at hh'
  have hp := h.dotProduct_mulVec_pos hv
  have hquad : (star v) ⬝ᵥ (metricBlock a b q *ᵥ v) = a-∑ i, ∑ k, inverse q i k*(b i*b k) := by
    have hmul0 : q 0 0*s 0+q 0 1*s 1=b 0 := by simpa [s,Fin.sum_univ_two] using inverse_mul_vector q hq b 0
    have hmul1 : q 1 0*s 0+q 1 1*s 1=b 1 := by simpa [s,Fin.sum_univ_two] using inverse_mul_vector q hq b 1
    have hbb : (∑ i, ∑ k, inverse q i k*(b i*b k)) = b 0*s 0+b 1*s 1 := by
      simp [s,Fin.sum_univ_two]
      ring
    rw [hbb]
    simp only [v,metricBlock,Matrix.of_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      star_trivial,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      one_mul,neg_mul,mul_neg]
    simp only [Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      mul_one]
    nlinarith [congrArg (fun t : ℝ => t * s 0) hmul0, congrArg (fun t : ℝ => t * s 1) hmul1]
  rwa [hquad] at hp

lemma cksMetric_normalized_positive {r : ℝ} (hr : r ≠ 0) {f : MassFields} {x : Point}
    (h : (cksMetric r f x).PosDef) :
    (cksQField (1/r) (normalizeMassFields r f) x).PosDef ∧ 0 < cksSchur r f x := by
  constructor
  · have hγ : (cksGamma r f x).PosDef := metricBlock_leaf_posDef h
    have he : cksQField (1/r) (normalizeMassFields r f) x = (1/r^2) • cksGamma r f x := by
      rw [cksGamma_normalized hr f,smul_smul]
      have hc : (1/r^2)*r^2=1 := by field_simp
      rw [hc,one_smul]
    rw [he]
    exact hγ.smul (one_div_pos.mpr (sq_pos_of_ne_zero hr))
  · exact metricBlock_schur_positive h

end
end CKSAngularGeometry

end

end OAI
