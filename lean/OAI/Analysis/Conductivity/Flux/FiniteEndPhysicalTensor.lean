import Mathlib
import OAI.Analysis.Conductivity.Branching.AttachedFlatTransport

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

local instance finiteEndPhysicalTensorMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance finiteEndPhysicalTensorBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

lemma measurable_real_matrix_mul {α : Type*} [MeasurableSpace α]
    {A B : α → Mat3} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x => A x*B x) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ (fun k _ => hA.eval.eval.mul hB.eval.eval)

lemma measurable_real_matrix_inverse : Measurable (fun A : Mat3 => A⁻¹) := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv']
  exact continuous_id.matrix_det.measurable.inv.smul
    continuous_id.matrix_adjugate.measurable

lemma measurable_sourceCartesianGradientMatrix (i j : Fin 4) :
    Measurable (sourceCartesianGradientMatrix i j) := by
  unfold sourceCartesianGradientMatrix
  exact measurable_real_matrix_mul (measurable_real_matrix_inverse.comp
    (continuous_sourceCollarJacobian i j).matrix_transpose.measurable)
      (continuous_sourceFaceAngleMatrix i j).measurable

lemma measurable_attachedCartesianMatrix (a : ℝ) (i j : Fin 4) :
    Measurable (attachedCartesianMatrix a i j) :=
  measurable_real_matrix_mul (measurable_sourceCartesianGradientMatrix i j) measurable_const

lemma measurable_sourceFlatDensity (i j : Fin 4) : Measurable (sourceFlatDensity i j) :=
  (continuous_sourceFaceAngleMatrix i j).matrix_det.measurable.div
    (continuous_sourceCollarJacobian i j).matrix_det.abs.measurable

def attachedVariableTensor (K : Coord3 → Mat3) (a : ℝ) (i j : Fin 4)
    (x : Coord3) : Mat3 :=
  (|a| *sourceFlatDensity i j x) •
    ((attachedCartesianMatrix a i j x)⁻¹ᵀ*K x*(attachedCartesianMatrix a i j x)⁻¹)

lemma attachedVariableTensor_measurable {K : Coord3 → Mat3} (hK : Measurable K)
    (a : ℝ) (i j : Fin 4) : Measurable (attachedVariableTensor K a i j) := by
  have hi := measurable_real_matrix_inverse.comp (measurable_attachedCartesianMatrix a i j)
  have ht := (continuous_id.matrix_transpose : Continuous (fun A : Mat3 => Aᵀ)).measurable.comp hi
  exact (measurable_const.mul (measurable_sourceFlatDensity i j)).smul (measurable_real_matrix_mul (measurable_real_matrix_mul ht hK) hi)

lemma attachedVariableTensor_symmetric {K : Coord3 → Mat3} (hK : ∀ x,(K x)ᵀ=K x)
    (a : ℝ) (i j : Fin 4) (x : Coord3) :
    (attachedVariableTensor K a i j x)ᵀ=attachedVariableTensor K a i j x := by
  simp only [attachedVariableTensor,Matrix.transpose_smul,Matrix.transpose_mul,
    Matrix.transpose_transpose,hK,Matrix.mul_assoc]

lemma attachedVariableTensor_energy (K : Coord3 → Mat3) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (v w : Coord3) :
    (attachedCartesianMatrix a i j x*ᵥv) ⬝ᵥ
      (attachedVariableTensor K a i j x*ᵥ(attachedCartesianMatrix a i j x*ᵥw))=
        |a| *sourceFlatDensity i j x*(v ⬝ᵥ(K x*ᵥw)) :=
  inverse_congruence_energy _ _ (attachedCartesianMatrix_det_ne_zero ha i j hx) _ _ _

lemma attachedVariableTensor_energy_density (K : Coord3 → Mat3) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (v w : Coord3) :
    |(sourceCollarJacobian i j x).det| *((attachedCartesianMatrix a i j x*ᵥv) ⬝ᵥ
      (attachedVariableTensor K a i j x*ᵥ(attachedCartesianMatrix a i j x*ᵥw)))=
        |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
          (v ⬝ᵥ(K x*ᵥw)) := by
  rw [attachedVariableTensor_energy K ha i j hx,sourceFlatDensity,sourceFaceAngleMatrix_det]
  field_simp [abs_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j hx)]

theorem attachedVariableTensor_elliptic {K : Coord3 → Mat3} {c C : ℝ}
    (hc : 0<c) (hcC : c≤C)
    (hK : ∀ x w,c*(w ⬝ᵥ w)≤w ⬝ᵥ(K x*ᵥw) ∧ w ⬝ᵥ(K x*ᵥw)≤C*(w ⬝ᵥ w))
    {a : ℝ} (ha : a≠0) (i j : Fin 4) :
    ∃ l L : ℝ,0<l ∧ l<L ∧ ∀ x∈sourceExtendedBox (-(1:ℝ)/100) (1/100),
      ∀ v : Coord3,l*‖v‖^2≤v ⬝ᵥ(attachedVariableTensor K a i j x*ᵥv) ∧
        v ⬝ᵥ(attachedVariableTensor K a i j x*ᵥv)≤L*‖v‖^2 := by
  obtain ⟨l,L,hl,hlL,hbound⟩ := attachedFlatTensor_elliptic ![1,0,1]
    (by intro x y; norm_num [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]; nlinarith [sq_nonneg x,sq_nonneg y]) ha i j
  refine ⟨c*l,C*L,mul_pos hc hl,?_,?_⟩
  · exact (mul_lt_mul_of_pos_left hlL hc).trans_le
      (mul_le_mul_of_nonneg_right hcC (hl.trans hlL).le)
  · intro x hx v
    let u := (attachedCartesianMatrix a i j x)⁻¹*ᵥv
    have hu : attachedCartesianMatrix a i j x*ᵥu=v := by
      dsimp [u]
      rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
        (isUnit_iff_ne_zero.mpr (attachedCartesianMatrix_det_ne_zero ha i j hx)),Matrix.one_mulVec]
    have hid : flatCylinderMatrix ![1,0,1]=(1:Mat3) := by
      ext k l
      fin_cases k <;> fin_cases l <;> rfl
    have href := attachedFlatTensor_energy ![1,0,1] ha i j hx u u
    rw [hu,hid,Matrix.one_mulVec] at href
    have he := attachedVariableTensor_energy K ha i j hx u u
    rw [hu] at he
    have hd : 0≤|a| *sourceFlatDensity i j x :=
      mul_nonneg (abs_nonneg _) (sourceFlatDensity_pos i j hx).le
    have hh := hK x u
    have hlow := mul_le_mul_of_nonneg_left hh.1 hd
    have hupp := mul_le_mul_of_nonneg_left hh.2 hd
    have hb := hbound x hx v
    rw [href] at hb
    rw [he]
    constructor
    · calc
        c*l*‖v‖^2 = c*(l*‖v‖^2) := by ring
        _ ≤ c*(|a| *sourceFlatDensity i j x*(u ⬝ᵥ u)) := mul_le_mul_of_nonneg_left hb.1 hc.le
        _ = |a| *sourceFlatDensity i j x*(c*(u ⬝ᵥ u)) := by ring
        _ ≤ _ := hlow
    · calc
        _ ≤ |a| *sourceFlatDensity i j x*(C*(u ⬝ᵥ u)) := hupp
        _ = C*(|a| *sourceFlatDensity i j x*(u ⬝ᵥ u)) := by ring
        _ ≤ C*(L*‖v‖^2) := mul_le_mul_of_nonneg_left hb.2 (hc.le.trans hcC)
        _ = C*L*‖v‖^2 := by ring

theorem attachedVariableTensor_energy_integral (K : Coord3 → Mat3) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (v w : Coord3 → Coord3) :
    (∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,
      attachedPhysicalFlatGradient a i j v y ⬝ᵥ
        (attachedVariableTensor K a i j (sourceCollarInverse i j y)*ᵥ
          attachedPhysicalFlatGradient a i j w y))=
      ∫ x in sourceExtendedBox l r,
        |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
          (v x ⬝ᵥ(K x*ᵥw x)) := by
  rw [sourceExtended_integral i j hl hr]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  have hx' : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100) := by
    obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp hx
    exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,hi,hj⟩
  simp only [attachedPhysicalFlatGradient,sourceCollarInverse_extended i j hl hr hx,smul_eq_mul]
  rw [sourceCollarDerivative_det,←sourceCollarJacobian_det]
  exact attachedVariableTensor_energy_density K ha i j hx' (v x) (w x)

end ScalarConductivity

end

end OAI
