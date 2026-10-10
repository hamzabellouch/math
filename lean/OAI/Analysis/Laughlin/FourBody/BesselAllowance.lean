import OAI.Analysis.Laughlin.Operators.OrthonormalRows
import OAI.Analysis.Laughlin.FourBody.PairTarget
import OAI.Analysis.Laughlin.FourBody.CopyOrthogonality

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators

theorem orthonormal_occupation_sum_bound {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (Q : ℕ) (c : I → J → ℝ) (v : J → Space Q)
    (hc : ∀ i k, (∑ j, c i j * c k j) = if i = k then 1 else 0) :
    (∑ i, occupationNormSq Q (∑ j, (c i j : ℂ) • v j)) ≤
      ∑ j, occupationNormSq Q (v j) := by
  unfold occupationNormSq
  simp only [map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro A hA
  exact orthonormal_rows_complex_bound c (fun j => (occupationBasis Q).repr (v j) A) hc

end Laughlin.Fock

namespace Laughlin.Spin
open scoped BigOperators

theorem source_fourBody_local_orthonormal (Q D : ℕ) (hQ : D+2 ≤ Q)
    (r s : OddPairLabel D) :
    (∑ b : LocalFourIndex D,
      fourBodyCoefficient Q (oddPairDeficit r) D D b.val.1.val b.val.2.1.val b.val.2.2.val *
      fourBodyCoefficient Q (oddPairDeficit s) D D b.val.1.val b.val.2.1.val b.val.2.2.val) =
      if r = s then 1 else 0 := by
  classical
  by_cases hrs : r = s
  · subst s
    simp only [ite_true]
    simpa only [pow_two] using source_fourBody_local_normalization Q (oddPairDeficit r) D
      (oddPairDeficit_le r) (oddPairDeficit_odd r) hQ
  · rw [ite_eq_right hrs]
    have hr : oddPairDeficit r ≤ Q := le_trans (oddPairDeficit_le r) (by omega)
    have hs : oddPairDeficit s ≤ Q := le_trans (oddPairDeficit_le s) (by omega)
    have hA : D-oddPairDeficit r ≤ 2*Q-2 := by have := oddPairDeficit_le r; omega
    have hB : D-oddPairDeficit r ≤ genericCoupledWeight Q Q (oddPairDeficit r) := by
      have := oddPairDeficit_le r; unfold genericCoupledWeight; omega
    have hC : D-oddPairDeficit s ≤ 2*Q-2 := by have := oddPairDeficit_le s; omega
    have hE : D-oddPairDeficit s ≤ genericCoupledWeight Q Q (oddPairDeficit s) := by
      have := oddPairDeficit_le s; unfold genericCoupledWeight; omega
    have hne : oddPairDeficit r ≠ oddPairDeficit s := by
      intro he
      exact hrs (Fin.ext (by unfold oddPairDeficit at he; omega))
    have ho := fourBodyCopy_orthogonal_pair Q (oddPairDeficit r) (oddPairDeficit s) D D 0 0
      hr hs (oddPairDeficit_odd r) (oddPairDeficit_odd s) hne hA hB hC hE
    rw [Fintype.sum_prod_type] at ho
    rw [← fourWeightSlice_sum Q D hQ (fun p j k =>
      fourBodyCoefficient Q (oddPairDeficit r) D D p j.val k.val *
        fourBodyCoefficient Q (oddPairDeficit s) D D p j.val k.val)]
    convert ho using 1
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro i hi
    by_cases he : p.val+i.val.1.val+i.val.2.val=D
    · rw [ite_eq_left he]
      have h1 := fourBodyCopy_source_coefficient Q (oddPairDeficit r) D D
        (oddPairDeficit_le r) (le_refl D) hQ p i he
      have h2 := fourBodyCopy_source_coefficient Q (oddPairDeficit s) D D
        (oddPairDeficit_le s) (le_refl D) hQ p i he
      simpa only [Nat.sub_self] using congrArg₂ (fun a b : ℝ => a*b) h1.symm h2.symm
    · rw [ite_eq_right he, fourBodyCopy_off Q (oddPairDeficit r) D 0 hr
        (oddPairDeficit_le r) hA hB p i (by simpa only [add_zero] using he),zero_mul]

end Laughlin.Spin

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators

theorem source_fourBody_bessel_allowance (Q D : ℕ) (hQ : D+2 ≤ Q) (x : Space Q) :
    (∑ r : OddPairLabel D, occupationNormSq Q
      (physicalFourCopyEnd Q (oddPairDeficit r) D (by have := oddPairDeficit_le r; omega) x)) ≤
      ∑ b : LocalFourIndex D, occupationNormSq Q (sourcePairEnd Q b.val.1.val x) := by
  simp only [physicalFourCopyEnd,LinearMap.sum_apply,LinearMap.smul_apply]
  apply (orthonormal_occupation_sum_bound Q
    (fun r : OddPairLabel D => fun b : LocalFourIndex D =>
      fourBodyCoefficient Q (oddPairDeficit r) D D b.val.1.val b.val.2.1.val b.val.2.2.val)
    (fun b => sourceFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ x)
    (source_fourBody_local_orthonormal Q D hQ)).trans
  exact Finset.sum_le_sum (fun b hb => sourceFour_normSq_le_pair Q b.val.1.val _ _ x)

theorem physical_fourBody_bessel_haar_allowance (Q D : ℕ) (hQ : D+2 ≤ Q)
    (x : Space Q) :
    (∑ r : OddPairLabel D, (2*Q-2+1 : ℕ) * (∫ g, occupationNormSq Q
      (physicalFourCopyEnd Q (oddPairDeficit r) D
        (by have := oddPairDeficit_le r; omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar)) ≤
      (Fintype.card (LocalFourIndex D) : ℝ) * sourceFockEnergy Q x := by
  have hL (r : OddPairLabel D) : Integrable
      (fun g => occupationNormSq Q (physicalFourCopyEnd Q (oddPairDeficit r) D
        (by have := oddPairDeficit_le r; omega) (exteriorRotation Q g⁻¹ x))) sourceHaar :=
    linearMap_rotation_norm_integrable Q _ x
  have hP (b : LocalFourIndex D) : Integrable
      (fun g => occupationNormSq Q (sourcePairEnd Q b.val.1.val
        (exteriorRotation Q g⁻¹ x))) sourceHaar :=
    linearMap_rotation_norm_integrable Q _ x
  have hi := integral_mono
    (integrable_finsetSum _ (fun (r : OddPairLabel D) hr => hL r))
    (integrable_finsetSum _ (fun (b : LocalFourIndex D) hb => hP b))
    (fun g => source_fourBody_bessel_allowance Q D hQ (exteriorRotation Q g⁻¹ x))
  rw [integral_finsetSum _ (fun (r : OddPairLabel D) hr => hL r)] at hi
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ (2*Q-2+1 : ℕ))).trans_eq
  rw [integral_finsetSum _ (fun (b : LocalFourIndex D) hb => hP b)]
  have hp (b : LocalFourIndex D) :
      (∫ g, occupationNormSq Q (sourcePairEnd Q b.val.1.val (exteriorRotation Q g⁻¹ x))
        ∂sourceHaar) = sourceFockEnergy Q x/(2*Q-2+1 : ℕ) :=
    physical_pair_norm_haar_real Q (by omega) ⟨b.val.1.val,by have := b.val.1.isLt; omega⟩ x
  simp_rw [hp]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hd : ((2*Q-2+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem source_bessel_allowance_count_fin :
    (∑ d : Fin 23, (d.val+2)^2/4) = 1222 := by decide +kernel

theorem physical_fourBody_total_bessel_haar_allowance (Q : ℕ) (hQ : 25 ≤ Q)
    (x : Space Q) :
    (∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1),
      (2*Q-2+1 : ℕ) * (∫ g, occupationNormSq Q
        (physicalFourCopyEnd Q (oddPairDeficit r) (d.val+1)
          (by have := oddPairDeficit_le r; omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar)) ≤
      1222 * sourceFockEnergy Q x := by
  calc
    _ ≤ ∑ d : Fin 23, ((d.val+2)^2/4 : ℕ) * sourceFockEnergy Q x := by
      apply Finset.sum_le_sum
      intro d hd
      simpa only [localFourIndex_card_retained (d.val+1) (by omega),Nat.add_assoc] using
        physical_fourBody_bessel_haar_allowance Q (d.val+1) (by omega) x
    _ = _ := by
      rw [← Finset.sum_mul,← Nat.cast_sum,source_bessel_allowance_count_fin,Nat.cast_ofNat]

theorem retainedFourAllowance_bessel_bound (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    retainedFourAllowance Q hQ x ≤ 1222*sourceFockEnergy Q x := by
  unfold retainedFourAllowance
  simp_rw [fourCopyForm_allowance_identity]
  exact physical_fourBody_total_bessel_haar_allowance Q hQ x

theorem sourceA4Form_retained_bessel_bound (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceA4Form Q x ≤ retainedFourTarget Q hQ x +
      (1222*(3/10^6 : ℝ)+averagedFourTransferError Q)*sourceFockEnergy Q x := by
  have ht := physical_fourBody_total_haar_transfer Q hQ x
  have ha := retainedFourAllowance_bessel_bound Q hQ x
  have he : (∑ d : Fin 23,
      (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*(d.val+1) : ℕ) : ℝ)) *
        (contractionForm Q (sourceFourFamilyEnd Q)
          (fourCopyOperator Q (d.val+1) (by omega) (finiteFourMiddle Q (d.val+1))) x).re) =
      retainedFourTarget Q hQ x+(3/10^6 : ℝ)*retainedFourAllowance Q hQ x-sourceA4Form Q x := by
    conv_lhs => arg 2; ext d; erw [fourCopyMiddleForm Q _ (by omega) (by omega) x]
    rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,sourceA4Form_retained Q hQ x]
    unfold retainedFourTarget retainedFourAllowance
    rw [Finset.mul_sum]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hi : -(averagedFourTransferError Q*sourceFockEnergy Q x) ≤
      retainedFourTarget Q hQ x+(3/10^6 : ℝ)*retainedFourAllowance Q hQ x-sourceA4Form Q x := by
    rw [← he]
    conv_rhs => arg 2; ext d; erw [fourCopyForm_scaled_haar]
    exact ht
  nlinarith

theorem sourceA4Form_bessel_bound (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceA4Form Q x ≤
      (∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x))) +
      (1222*(3/10^6 : ℝ)+averagedFourTransferError Q)*sourceFockEnergy Q x := by
  have ht := retainedFourTarget_le_full Q hQ x
  rw [fourPairTargetMatrix_Fock] at ht
  have hb := sourceA4Form_retained_bessel_bound Q hQ x
  linarith

end Laughlin.Fock

end OAI
