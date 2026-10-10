import Mathlib
import OAI.MathematicalPhysics.BFSS.FermionQuantization

namespace OAI

/-! Exact field-frequency identification and quantitative frequency lower bounds. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset BFSSSpinHalf
open scoped Kronecker
variable {N : ℕ} (M : AlgebraData N)

lemma colorEuclidean_matrix_entry (L : Module.End ℝ (ColorVector N)) (A B : ColorIndex N) :
    (eucAlg.symm L) A B = (L (EuclideanSpace.single B 1)) A := by
  have h := congrArg (fun K : Module.End ℝ (ColorVector N) =>
    (K (EuclideanSpace.single B 1)) A) (eucAlg.apply_symm_apply L)
  change ((eucAlg.symm L)*ᵥ (Pi.single B 1)) A = _ at h
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply] using h

lemma colorJ_matrix_entry (q : Boson N) (a : Fin 3) (A B : ColorIndex N) :
    (eucAlg.symm (M.colorJ q a)) A B =
      (1/2:ℝ) * ∑ C : ColorIndex N,
        M.structureConstant B A C * q (Fin.castLE (by decide) a,C) := by
  rw [colorEuclidean_matrix_entry]
  change ((1/2:ℝ) • M.colorLie (spatialColor q (Fin.castLE (by decide) a))
    (EuclideanSpace.single B 1)) A = _
  simp only [PiLp.smul_apply,smul_eq_mul,colorLie,PiLp.toLp_apply,spatialColor]
  congr 1
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.sum_eq_single B]
  · simp only [PiLp.single_eq_same,mul_one]
    rw [←M.structureConstant_cycle B A C]
  · intro D _ hDB
    have hz : EuclideanSpace.single B (1:ℝ) D = 0 := by
      simp [hDB]
    rw [hz,mul_zero]
  · simp

lemma normal_frequency_tensor_entry (q : Boson N) (a : Fin 3)
    (r s : FrequencyIndex N) :
    (leftLift (κ := ColorIndex N) (M.gamma (Fin.castLE (by decide) a))*M.colorJTensor q a) r s =
      M.gamma (Fin.castLE (by decide) a) r.1 s.1 *
        ((1/2:ℝ) * ∑ C : ColorIndex N,
          M.structureConstant s.2 r.2 C * q (Fin.castLE (by decide) a,C)) := by
  have hm : leftLift (κ := ColorIndex N) (M.gamma (Fin.castLE (by decide) a))*M.colorJTensor q a =
      (M.gamma (Fin.castLE (by decide) a)) ⊗ₖ (eucAlg.symm (M.colorJ q a)) := by
    change ((M.gamma (Fin.castLE (by decide) a)) ⊗ₖ (1 : Matrix (ColorIndex N) (ColorIndex N) ℝ)) *
      ((1 : GammaMatrix) ⊗ₖ (eucAlg.symm (M.colorJ q a))) = _
    rw [←Matrix.mul_kronecker_mul,mul_one,one_mul]
  rw [hm,Matrix.kronecker_apply,M.colorJ_matrix_entry]

lemma zero_relations_coordinate_tail (q : Boson N) (hq : M.ZeroRelations q)
    (j : SpaceIndex) (hj : 3 ≤ j.val) (C : ColorIndex N) : q (j,C) = 0 := by
  have h := congrArg (fun v : ColorVector N => v C) (hq.2.2.2 j hj)
  exact h

theorem fermionCoefficient_eq_normalFrequency (q : Boson N)
    (hq : M.deformedBosonicPotential 1 1 q = 0) :
    M.fermionCoefficient q = M.normalFermionFrequency q := by
  have hqr := M.potential_zero_relations q hq
  ext r s
  have ht : (∑ j : SpaceIndex, ∑ C : ColorIndex N,
      M.structureConstant s.2 r.2 C*q (j,C)*M.gamma j r.1 s.1) =
      ∑ j ∈ BFSSGamma.firstThree, ∑ C : ColorIndex N,
        M.structureConstant s.2 r.2 C*q (j,C)*M.gamma j r.1 s.1 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    apply Finset.sum_eq_zero
    intro C _
    have hge : 3 ≤ j.val := by
      have h := mt (BFSSGamma.mem_firstThree j).mpr hj
      exact Nat.le_of_not_gt h
    rw [M.zero_relations_coordinate_tail q hqr j hge C,mul_zero,zero_mul]
  have h0 := M.normal_frequency_tensor_entry q 0 r s
  have h1 := M.normal_frequency_tensor_entry q 1 r s
  have h2 := M.normal_frequency_tensor_entry q 2 r s
  change (leftLift (κ := ColorIndex N) (M.gamma 0)*M.colorJTensor q 0) r s =
    M.gamma 0 r.1 s.1 * ((1/2:ℝ) * ∑ C : ColorIndex N,
      M.structureConstant s.2 r.2 C*q (0,C)) at h0
  change (leftLift (κ := ColorIndex N) (M.gamma 1)*M.colorJTensor q 1) r s =
    M.gamma 1 r.1 s.1 * ((1/2:ℝ) * ∑ C : ColorIndex N,
      M.structureConstant s.2 r.2 C*q (1,C)) at h1
  change (leftLift (κ := ColorIndex N) (M.gamma 2)*M.colorJTensor q 2) r s =
    M.gamma 2 r.1 s.1 * ((1/2:ℝ) * ∑ C : ColorIndex N,
      M.structureConstant s.2 r.2 C*q (2,C)) at h2
  simp only [fermionCoefficient,ht,normalFermionFrequency,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.add_apply,h0,h1,h2]
  have hT : leftLift (κ := ColorIndex N) (BFSSGamma.massT M.gamma) r s =
      BFSSGamma.massT M.gamma r.1 s.1 * (if r.2 = s.2 then 1 else 0) := rfl
  rw [hT]
  simp only [BFSSGamma.firstThree,
    Finset.sum_insert (by decide : (0 : Fin 9) ∉ ({1,2} : Finset (Fin 9))),
    Finset.sum_insert (by decide : (1 : Fin 9) ∉ ({2} : Finset (Fin 9))),
    Finset.sum_singleton,←Finset.sum_mul]
  by_cases he : r.2 = s.2 <;> simp only [he,ite_true,ite_false,mul_one,mul_zero] <;> ring

end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open BFSSSpinHalf
variable {N : ℕ} (M : AlgebraData N)

lemma normalFermionFrequency_skew (q : Boson N) :
    (M.normalFermionFrequency q).transpose = -M.normalFermionFrequency q := by
  have hg (a : SpaceIndex) : (M.gamma a).transpose = M.gamma a := (M.gamma_symmetric a).eq
  have hc (a : Fin 3) :
      M.colorJTensor q a * leftLift (M.gamma (Fin.castLE (by decide) a)) =
        leftLift (M.gamma (Fin.castLE (by decide) a)) * M.colorJTensor q a :=
    (lifts_commute _ _).eq.symm
  have term (a : Fin 3) :
      (leftLift (κ := ColorIndex N) (M.gamma (Fin.castLE (by decide) a))*M.colorJTensor q a).transpose =
      -(leftLift (M.gamma (Fin.castLE (by decide) a))*M.colorJTensor q a) := by
    rw [Matrix.transpose_mul,M.colorJTensor_skew,leftLift_transpose,hg,neg_mul,hc]
  have h0 := term 0
  have h1 := term 1
  have h2 := term 2
  change (leftLift (M.gamma 0)*M.colorJTensor q 0).transpose = -(leftLift (M.gamma 0)*M.colorJTensor q 0) at h0
  change (leftLift (M.gamma 1)*M.colorJTensor q 1).transpose = -(leftLift (M.gamma 1)*M.colorJTensor q 1) at h1
  change (leftLift (M.gamma 2)*M.colorJTensor q 2).transpose = -(leftLift (M.gamma 2)*M.colorJTensor q 2) at h2
  simp only [normalFermionFrequency,Matrix.transpose_sub,Matrix.transpose_smul,
    Matrix.transpose_add,h0,h1,h2,leftLift_transpose,
    BFSSGamma.massT_transpose M.gamma M.gamma_clifford M.gamma_symmetric,map_neg]
  module

theorem normalFermionFrequency_norm_lower (q : Boson N)
    (hq : M.deformedBosonicPotential 1 1 q = 0)
    (x : EuclideanSpace ℝ (FrequencyIndex N)) :
    (1/2 : ℝ) * ‖x‖ ≤ ‖eucAlg (M.normalFermionFrequency q) x‖ := by
  let T : FrequencyMatrix N := leftLift (BFSSGamma.massT M.gamma)
  let A : FrequencyMatrix N := (3/2:ℝ) • 1-(4:ℝ) • M.spinHalfCoupling q
  have ht : T*T = -(1 : FrequencyMatrix N) := by
    change leftLift (BFSSGamma.massT M.gamma)*leftLift (BFSSGamma.massT M.gamma) = _
    rw [←map_mul,BFSSGamma.massT_sq M.gamma M.gamma_clifford M.gamma_symmetric,map_neg,map_one]
  have hts : T.transpose = -T := by
    simp only [T,leftLift_transpose,
      BFSSGamma.massT_transpose M.gamma M.gamma_clifford M.gamma_symmetric,map_neg]
  have hnorm (y : EuclideanSpace ℝ (FrequencyIndex N)) : ‖eucAlg T y‖ = ‖y‖ := by
    have he := skew_inner T hts y (eucAlg T y)
    change inner ℝ (eucAlg T y) (eucAlg T y) = -inner ℝ y ((eucAlg T*eucAlg T) y) at he
    rw [←map_mul,ht,map_neg,map_one,LinearMap.neg_apply,Module.End.one_apply,inner_neg_right,
      neg_neg,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at he
    nlinarith [norm_nonneg y,norm_nonneg (eucAlg T y)]
  have hp := congrArg (eucAlg (ι := FrequencyIndex N))
    (M.spinHalfCoupling_polynomial q (M.potential_zero_relations q hq))
  simp only [map_mul,map_add,map_smul] at hp
  have hb := shift_norm_lower (fun i => eucAlg (M.colorJTensor q i)) (eucAlg (M.spinHalfCoupling q))
    (fun i => skew_inner _ (M.colorJTensor_skew q i))
    (symmetric_inner _ (M.spinHalfCoupling_symmetric q)) hp x
  rw [M.normalFermionFrequency_factor]
  change (1/2:ℝ)*‖x‖ ≤ ‖eucAlg (T*A) x‖
  rw [map_mul,Module.End.mul_apply,hnorm]
  simpa only [A,map_sub,map_smul,map_one,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply] using hb
end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
variable {N : ℕ} (M : AlgebraData N)

theorem normal_fermion_field_exact (q : Boson N)
    (hq : M.deformedBosonicPotential 1 1 q = 0) :
    M.deformedFermionField 1 1 q =
      (M.quantizeFrequency (M.normalFermionFrequency q)).restrictScalars ℝ := by
  rw [M.deformedFermionField_quantized,M.fermionCoefficient_eq_normalFrequency q hq]

end
end BFSSQuantum.AlgebraData

end OAI
