import OAI.Analysis.Laughlin.FourBody.CopyFormAllowance
import OAI.Analysis.Laughlin.FourBody.GlobalFock
import OAI.Analysis.Laughlin.FourBody.MiddleForm
import OAI.Analysis.Laughlin.FourBody.TotalTransfer

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators Matrix

noncomputable def retainedFourTarget (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) : ℝ :=
  ∑ d : Fin 23, (contractionForm Q (sourceFourFamilyEnd Q)
    (retainedFourInclusion Q (d.val+1) (by omega) (firstOddPairLabel (d.val+1) (by omega)) *
      (retainedFourInclusion Q (d.val+1) (by omega) (firstOddPairLabel (d.val+1) (by omega)))ᴴ) x).re

theorem fourCopyForm_scaled_haar (Q D : ℕ) (hQ : D+2 ≤ Q)
    (C : OddPairLabel D → OddPairLabel D → ℝ) (x : Space Q) :
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ C) x).re =
    ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, occupationQuadratic Q C
      (fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
        (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) := by
  rw [← physical_fourCopyOperator_haar Q D hQ C x]
  have hd : ((4*Q-1-2*D : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 4*Q-1-2*D ≠ 0 by omega)
  field_simp

theorem sourceA4Form_retained_bound (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceA4Form Q x ≤ retainedFourTarget Q hQ x +
      (10946*(3/10^6 : ℝ)+averagedFourTransferError Q)*sourceFockEnergy Q x := by
  have ht := physical_fourBody_total_haar_transfer Q hQ x
  have ha := retainedFourAllowance_bound Q hQ x
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

end Laughlin.Fock

end OAI
