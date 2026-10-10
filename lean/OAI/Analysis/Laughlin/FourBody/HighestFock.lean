import OAI.Analysis.Laughlin.Fock.RankOneHaar
import OAI.Analysis.Laughlin.FourBody.FockCovariance
import OAI.Analysis.Laughlin.FourBody.MultiplicityHaar
import OAI.Analysis.Laughlin.FourBody.WeightSlice

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem physicalFourCopyEnd_column (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) (x : Space Q) :
    (∑ i, star (retainedFourInclusion Q D hQ r i 0) • sourceFourFamilyEnd Q i x) =
      physicalFourCopyEnd Q (oddPairDeficit r) D (by omega) x := by
  have hc (i : FourWedgeIndex Q) :
      star (retainedFourInclusion Q D hQ r i 0) • sourceFourFamilyEnd Q i x =
        if i.1.val+i.2.val.1.val+i.2.val.2.val=D then
          (fourBodyCoefficient Q (oddPairDeficit r) D D i.1.val i.2.val.1.val i.2.val.2.val : ℂ) •
            sourceFourEnd Q i.1.val i.2.val.1 i.2.val.2 x else 0 := by
    rw [retainedFourInclusion_column]
    simp only [Fin.val_zero,Complex.star_def,Complex.conj_ofReal]
    by_cases h : i.1.val+i.2.val.1.val+i.2.val.2.val=D
    · have he := fourBodyCopy_source_coefficient Q (oddPairDeficit r) D D
        (oddPairDeficit_le r) (le_refl D) hQ i.1 i.2 h
      simp only [Nat.sub_self] at he
      rw [ite_eq_left h,he]
      rfl
    · rw [ite_eq_right h,fourBodyCopy_off Q (oddPairDeficit r) D 0 _ (oddPairDeficit_le r)
        _ _ i.1 i.2 (by simpa using h)]
      simp
  simp_rw [hc]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [fourWeightSlice_sum Q D hQ (fun p j k =>
    (fourBodyCoefficient Q (oddPairDeficit r) D D p j.val k.val : ℂ) • sourceFourEnd Q p j k x)]
  simp only [physicalFourCopyEnd,LinearMap.sum_apply,LinearMap.smul_apply]

theorem contractionForm_outer_cross {I : Type*} [Fintype I] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (v w : I → ℂ) (x : Space Q) :
    contractionForm Q minus (complexOuter v w) x =
      occupationInner Q (∑ i, star (v i) • minus i x) (∑ j, star (w j) • minus j x) := by
  simp only [occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,star_star,contractionForm,complexOuter,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem matrix_cross_sandwich_single {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (V W : Matrix I J ℂ) (p : J) :
    V*diagonalUnit p*Wᴴ = complexOuter (fun i => V i p) (fun i => W i p) := by
  ext i j
  simp [diagonalUnit,Matrix.mul_apply,complexOuter,Matrix.conjTranspose_apply,ite_and]

theorem physicalFourCopyEnd_cross_haar (Q D : ℕ) (hQ : D+2 ≤ Q) (r s : OddPairLabel D)
    (x : Space Q) :
    ((4*Q-1-2*D : ℕ) : ℂ) * (∫ g, occupationInner Q
      (physicalFourCopyEnd Q (oddPairDeficit r) D (by omega) (exteriorRotation Q g⁻¹ x))
      (physicalFourCopyEnd Q (oddPairDeficit s) D (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      contractionForm Q (sourceFourFamilyEnd Q)
        (retainedFourInclusion Q D hQ r * (retainedFourInclusion Q D hQ s)ᴴ) x := by
  let M : Matrix (Fin (fourSpinWeight Q D+1)) (Fin (fourSpinWeight Q D+1)) ℂ := diagonalUnit 0
  have h := contractionForm_haar Q (fourBodySpinRepresentation Q)
    (fourBodySpinRepresentation_inv Q) (fourBodySpinRepresentation_continuous Q)
    (sourceFourFamilyEnd Q) (sourceFourFamilyEnd_rotation Q (by omega))
    (retainedFourInclusion Q D hQ r*M*(retainedFourInclusion Q D hQ s)ᴴ) x
  rw [fourBody_cross_orbit,contractionForm_smul] at h
  have ht : Matrix.trace M=1 := by simp [M,diagonalUnit,Matrix.trace,Matrix.diag]
  rw [ht] at h
  have he := matrix_cross_sandwich_single (retainedFourInclusion Q D hQ r)
    (retainedFourInclusion Q D hQ s) (0 : Fin (fourSpinWeight Q D+1))
  change retainedFourInclusion Q D hQ r*M*(retainedFourInclusion Q D hQ s)ᴴ = _ at he
  simp_rw [he,contractionForm_outer_cross,physicalFourCopyEnd_column] at h
  rw [h]
  have hd : ((4*Q-1-2*D : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show 4*Q-1-2*D ≠ 0 by omega)
  field_simp

end Laughlin.Fock

end OAI
