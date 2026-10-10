import OAI.Analysis.Laughlin.FourBody.ErrorMatrix
import OAI.Analysis.Laughlin.FourBody.OccupationCoefficient
import OAI.Analysis.Laughlin.Operators.FourOccupationEquiv

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Spin

private theorem sqrt_weight_product (u v f : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hf : 0 ≤ f) :
    Real.sqrt (u/f)*Real.sqrt (v/f) = Real.sqrt (u*v)/f := by
  rw [Real.sqrt_div hu,Real.sqrt_div hv]

  rw [div_mul_div_comm,Real.mul_self_sqrt hf,← Real.sqrt_mul hu]

private theorem fourOccupation_product (Q r s D : ℕ) (A : FourOccupation Q D) :
    fourOccupationCoefficient Q r D A.val * fourOccupationCoefficient Q s D A.val =
      let t := (occupationQuadruple Q D A).val
      Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) *
        ((Certificate.L D r t : ℝ)*(Certificate.L D s t : ℝ) /
          ((t.1.factorial : ℝ)*t.2.1.factorial*t.2.2.1.factorial*t.2.2.2.factorial)) := by
  simp only [fourOccupationCoefficient,dite_eq_left A.property.1,ite_eq_left A.property.2,occupationQuadruple]
  have hr : 0 ≤ sourceCopyWeight D r := by unfold sourceCopyWeight; positivity
  have hs : 0 ≤ sourceCopyWeight D s := by unfold sourceCopyWeight; positivity
  have hf : 0 ≤ (((occupationFourLabels Q A.val A.property.1 0).val.factorial : ℝ) *
    (occupationFourLabels Q A.val A.property.1 1).val.factorial *
    (occupationFourLabels Q A.val A.property.1 2).val.factorial *
    (occupationFourLabels Q A.val A.property.1 3).val.factorial) := by positivity
  rw [show ∀ a b c d : ℝ, (a*b)*(c*d)=(a*c)*(b*d) from by intros; ring,
    sqrt_weight_product _ _ _ hr hs hf]
  ring

theorem source_fourBody_physical_Gram (Q r s D : ℕ) (hQ : D+1 ≤ Q)
    (hr : r ≤ D) (hs : s ≤ D) (hor : Odd r) (hos : Odd s) :
    occupationInner Q (limitFourColumn Q r D) (limitFourColumn Q s D) =
      ((Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) *
        (Certificate.Z D r s : ℝ) : ℝ) : ℂ) := by
  classical
  rw [limitFourColumn_gram_occupation Q r s D hr hs hor hos]
  congr 1
  let P := fun A : Finset (Fin (Q+1)) => A.card=4 ∧ (∑ i ∈ A, i.val)=D+1
  let f := fun A => fourOccupationCoefficient Q r D A * fourOccupationCoefficient Q s D A
  have hsum : ∑ A, f A = ∑ A ∈ Finset.univ.filter P, f A := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro A hA hn
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hn
    by_cases hc : A.card=4
    · have hw : (∑ i ∈ A, i.val) ≠ D+1 := by intro hw; exact hn ⟨hc,hw⟩
      simp [f,fourOccupationCoefficient,hc,hw]
    · simp [f,fourOccupationCoefficient,hc]
  change ∑ A, f A = _
  rw [hsum,Finset.sum_subtype (p := P) (Finset.univ.filter P) (by simp)]
  change (∑ A : FourOccupation Q D, fourOccupationCoefficient Q r D A.val *
    fourOccupationCoefficient Q s D A.val) = _
  simp_rw [fourOccupation_product]
  rw [← Finset.mul_sum,sum_fourOccupations Q D hQ (fun t =>
    (Certificate.L D r t : ℝ)*(Certificate.L D s t : ℝ) /
      ((t.1.factorial : ℝ)*t.2.1.factorial*t.2.2.1.factorial*t.2.2.2.factorial))]
  simp only [Certificate.Z]
  push_cast
  simp only [List.map_map,Function.comp_def]
  push_cast
  rfl

theorem source_fourBody_physical_scaledGram (Q D : ℕ) (hQ : D+1 ≤ Q)
    (i j : Fin ((D+1)/2)) :
    occupationInner Q (limitFourColumn Q (Certificate.copyLabel i) D)
      (limitFourColumn Q (Certificate.copyLabel j) D) =
      (Certificate.scaledGram D i j : ℂ) := by
  have hi : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hj : Certificate.copyLabel j ≤ D := by unfold Certificate.copyLabel; have := j.isLt; omega
  rw [source_fourBody_physical_Gram Q _ _ D hQ hi hj
    ⟨i.val,by unfold Certificate.copyLabel; omega⟩ ⟨j.val,by unfold Certificate.copyLabel; omega⟩,
    sourceCopyWeight_certificate,sourceCopyWeight_certificate,
    Real.sqrt_mul (Certificate.copyWeight_nonneg D i)]
  simp only [Certificate.scaledGram,Certificate.weightSqrtDiagonal,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.map_apply,Certificate.gramRational,Rat.coe_castHom]
  push_cast
  ring

end Laughlin.Fock

end OAI
