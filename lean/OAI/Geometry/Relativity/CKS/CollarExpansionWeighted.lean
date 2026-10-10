import OAI.Geometry.Relativity.CKS.CollarExpansionJet

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def radialCorrection (b : MatrixScalarJet) : ExpansionInput := (0,0,b,0,0)

def collarExpansionInput (e θ : ℝ) (j : ExpansionInput)
    (q : MatrixScalarJet) (dq : I → MatrixScalarJet) : ExpansionInput :=
  (1-e) • j+e • expansionReference q dq+radialCorrection (θ • (q-j.1))

lemma radialCorrection_norm (b : MatrixScalarJet) : ‖radialCorrection b‖ = ‖b‖ := by
  simp [radialCorrection,Prod.norm_def,norm_nonneg]

lemma radialCorrection_reference_bound (θ : ℝ) (j : ExpansionInput)
    (q : MatrixScalarJet) (dq : I → MatrixScalarJet) :
    ‖radialCorrection (θ • (q-j.1))‖ ≤ |θ| *‖j-expansionReference q dq‖ := by
  rw [radialCorrection_norm,norm_smul,Real.norm_eq_abs,norm_sub_rev]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact norm_fst_le (j-expansionReference q dq)

lemma collarExpansion_difference (e θ : ℝ) (he : 0 ≤ e) (j : ExpansionInput)
    (q : MatrixScalarJet) (dq : I → MatrixScalarJet) :
    ‖collarExpansionInput e θ j q dq-j‖ ≤ (e+|θ|)*‖j-expansionReference q dq‖ := by
  have hlin : (1-e) • j+e • expansionReference q dq-j =
      -e • (j-expansionReference q dq) := by module
  calc
    _ = ‖-e • (j-expansionReference q dq)+radialCorrection (θ • (q-j.1))‖ := by
      congr 1
      rw [collarExpansionInput,← hlin]
      abel
    _ ≤ ‖-e • (j-expansionReference q dq)‖+‖radialCorrection (θ • (q-j.1))‖ := norm_add_le _ _
    _ ≤ |(-e)| *‖j-expansionReference q dq‖+|θ| *‖j-expansionReference q dq‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add le_rfl (radialCorrection_reference_bound θ j q dq)
    _ = _ := by rw [abs_neg,abs_of_nonneg he]; ring

lemma collarExpansion_reference_bound (e θ : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (j : ExpansionInput) (q : MatrixScalarJet) (dq : I → MatrixScalarJet) :
    ‖collarExpansionInput e θ j q dq-expansionReference q dq‖ ≤
      (1+|θ|)*‖j-expansionReference q dq‖ := by
  have hlin : (1-e) • j+e • expansionReference q dq-expansionReference q dq =
      (1-e) • (j-expansionReference q dq) := by module
  calc
    _ = ‖(1-e) • (j-expansionReference q dq)+radialCorrection (θ • (q-j.1))‖ := by
      congr 1
      rw [collarExpansionInput,← hlin]
      abel
    _ ≤ ‖(1-e) • (j-expansionReference q dq)‖+‖radialCorrection (θ • (q-j.1))‖ := norm_add_le _ _
    _ ≤ (1-e)*‖j-expansionReference q dq‖+|θ| *‖j-expansionReference q dq‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr he1)]
      exact add_le_add le_rfl (radialCorrection_reference_bound θ j q dq)
    _ ≤ _ := by nlinarith [mul_nonneg he (norm_nonneg (j-expansionReference q dq))]

theorem weighted_expansion {K : Set ExpansionInput} (hK : IsCompact K)
    (hreg : K ⊆ expansionRegion) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : ExpansionInput) (q : MatrixScalarJet) (dq : I → MatrixScalarJet)
        (r e θ w A B : ℝ),
      expansionReference q dq ∈ K → 0 < r → 0 ≤ e → e ≤ 1 →
      e ≤ w → 0 ≤ w → w ≤ 1 → 0 ≤ A → 0 ≤ B →
      ‖j-expansionReference q dq‖ ≤ A/r^3 → |θ| ≤ B*w →
      (1+B)*A/r^3 ≤ δ →
      ‖normalizedExpansionJet (collarExpansionInput e θ j q dq)-normalizedExpansionJet j‖ ≤
        C*(1+B)*A*w/r^3 := by
  obtain ⟨δ,hδ,C,hC⟩ := expansion_uniform_lipschitz hK hreg
  refine ⟨δ,hδ,C,C.coe_nonneg,?_⟩
  intro j q dq r e θ w A B href hr he he1 hew hw hw1 hA hB hsmall hθ hδ'
  have hAr : 0 ≤ A/r^3 := div_nonneg hA (pow_nonneg hr.le _)
  have hBθ : |θ| ≤ B := hθ.trans (mul_le_of_le_one_right hB hw1)
  have hj : j ∈ Metric.cthickening δ K := by
    apply Metric.mem_cthickening_of_dist_le j (expansionReference q dq) δ K href
    rw [dist_eq_norm]
    apply hsmall.trans
    calc
      A/r^3 ≤ (1+B)*(A/r^3) := le_mul_of_one_le_left hAr (by linarith)
      _ = (1+B)*A/r^3 := by ring
      _ ≤ δ := hδ'
  have hnew : collarExpansionInput e θ j q dq ∈ Metric.cthickening δ K := by
    apply Metric.mem_cthickening_of_dist_le (collarExpansionInput e θ j q dq)
      (expansionReference q dq) δ K href
    rw [dist_eq_norm]
    apply (collarExpansion_reference_bound e θ he he1 j q dq).trans
    calc
      _ ≤ (1+|θ|)*(A/r^3) := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ (1+B)*(A/r^3) := mul_le_mul_of_nonneg_right (by linarith) hAr
      _ = (1+B)*A/r^3 := by ring
      _ ≤ δ := hδ'
  have hdiff : ‖collarExpansionInput e θ j q dq-j‖ ≤ (1+B)*A*w/r^3 := by
    apply (collarExpansion_difference e θ he j q dq).trans
    calc
      _ ≤ (e+|θ|)*(A/r^3) := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ (w+B*w)*(A/r^3) := mul_le_mul_of_nonneg_right (add_le_add hew hθ) hAr
      _ = _ := by ring
  exact (hC.norm_sub_le hnew hj).trans (by
    calc
      _ ≤ (C:ℝ)*((1+B)*A*w/r^3) := mul_le_mul_of_nonneg_left hdiff C.coe_nonneg
      _ = _ := by ring)

end
end CKSAngularGeometry

end

end OAI
