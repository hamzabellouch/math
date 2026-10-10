import OAI.Geometry.Relativity.CKS.CKSMetricPositivity

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix

 def foliationMetric (U : ℝ) (γ : Mat) (s : Point) : AmbientMat :=
  metricBlock (1/U^2+∑ a, ∑ b, γ a b*s a*s b) (fun a => ∑ b, γ a b*s b) γ

 def foliationNormal (U : ℝ) (s : Point) : Fin 3 → ℝ := ![U,-U*s 0,-U*s 1]

 def foliationTensor (U L : ℝ) (η : Point) (kT : Mat) (s : Point) : AmbientMat :=
  metricBlock (L/U^2+2/U*(∑ a, η a*s a)+∑ a, ∑ b, kT a b*s a*s b)
    (fun a => η a/U+∑ b, kT a b*s b) kT

lemma hermitian_real_symmetry {n : Type*} {q : Matrix n n ℝ} (h : q.IsHermitian) (i j : n) :
    q j i=q i j := by
  simpa only [conjTranspose_apply,star_trivial] using congrFun (congrFun h i) j

lemma metricBlock_hermitian (a : ℝ) (b : Point) {q : Mat} (hq : q.IsHermitian) :
    (metricBlock a b q).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTranspose_apply,metricBlock,hermitian_real_symmetry hq 0 1]

lemma foliationMetric_quadratic (U : ℝ) {γ : Mat} (hγ : γ.IsHermitian) (s : Point)
    (v : Fin 3 → ℝ) :
    star v ⬝ᵥ (foliationMetric U γ s *ᵥ v) =
      (v 0/U)^2+star (fun a : Fin 2 => v a.succ+s a*v 0) ⬝ᵥ
        (γ *ᵥ (fun a : Fin 2 => v a.succ+s a*v 0)) := by
  simp only [foliationMetric,metricBlock,Matrix.of_apply,mulVec,dotProduct,Fin.sum_univ_three,
    Fin.sum_univ_two,star_trivial,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.tail_cons]
  simp only [Fin.succ_zero_eq_one',Fin.succ_one_eq_two']
  rw [hermitian_real_symmetry hγ 0 1]
  ring

theorem foliationMetric_posDef {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.PosDef) (s : Point) :
    (foliationMetric U γ s).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (metricBlock_hermitian _ _ hγ.isHermitian)
  intro v hv
  change 0 < star v ⬝ᵥ (foliationMetric U γ s *ᵥ v)
  rw [foliationMetric_quadratic U hγ.isHermitian s v]
  let y : Point := fun a => v a.succ+s a*v 0
  have hy0 := hγ.posSemidef.dotProduct_mulVec_nonneg y
  by_cases h0 : v 0=0
  · have hy : y ≠ 0 := by
      intro hy
      apply hv
      ext i
      fin_cases i
      · exact h0
      · have hh := congrFun hy 0; simpa [y,h0] using hh
      · have hh := congrFun hy 1; simpa [y,h0] using hh
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (hγ.dotProduct_mulVec_pos hy)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (div_ne_zero h0 hU)) hy0

lemma foliationNormal_unit {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian) (s : Point) :
    star (foliationNormal U s) ⬝ᵥ (foliationMetric U γ s *ᵥ foliationNormal U s)=1 := by
  rw [foliationMetric_quadratic U hγ s]
  have hy : (fun a : Fin 2 => foliationNormal U s a.succ+s a*foliationNormal U s 0)=0 := by
    ext a; fin_cases a <;> simp [foliationNormal,mul_comm]
  rw [hy]
  simp [foliationNormal,hU]

lemma foliationNormal_orthogonal {U : ℝ} (_hU : U ≠ 0) {γ : Mat} (_hγ : γ.IsHermitian)
    (s : Point) (a : Fin 2) :
    ∑ j : Fin 3, foliationMetric U γ s a.succ j*foliationNormal U s j=0 := by
  fin_cases a <;> norm_num [Fin.succ,Fin.sum_univ_three,foliationMetric,metricBlock,Matrix.of_apply,foliationNormal,
    Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.head_fin_const,Matrix.tail_cons,Matrix.cons_val_fin_one] <;> ring

lemma foliationTensor_normal {U L : ℝ} (hU : U ≠ 0) (η : Point) {kT : Mat}
    (hk : kT.IsHermitian) (s : Point) :
    star (foliationNormal U s) ⬝ᵥ (foliationTensor U L η kT s *ᵥ foliationNormal U s)=L := by
  simp only [foliationTensor,foliationNormal,metricBlock,Matrix.of_apply,mulVec,dotProduct,Fin.sum_univ_three,
    Fin.sum_univ_two,star_trivial,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.tail_cons]
  rw [hermitian_real_symmetry hk 0 1]
  field_simp
  ring

lemma foliationTensor_mixed {U L : ℝ} (hU : U ≠ 0) (η : Point) (kT : Mat) (s : Point) (a : Fin 2) :
    ∑ j : Fin 3, foliationTensor U L η kT s a.succ j*foliationNormal U s j=η a := by
  fin_cases a <;> norm_num [Fin.succ,foliationTensor,foliationNormal,metricBlock,Matrix.of_apply,Fin.sum_univ_three,
    Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.head_fin_const,Matrix.tail_cons,Matrix.cons_val_fin_one] <;>
    field_simp <;> ring

lemma foliationTensor_leaf (U L : ℝ) (η : Point) (kT : Mat) (s : Point) :
    (foliationTensor U L η kT s).submatrix Fin.succ Fin.succ=kT :=
  metricBlock_submatrix _ _ _

end
end CKSAngularGeometry

end

end OAI
