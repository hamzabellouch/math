import OAI.Analysis.Laughlin.FourBody.HaarTransfer

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators

theorem physical_fourBody_total_haar_transfer (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    -(averagedFourTransferError Q * sourceFockEnergy Q x) ≤
      ∑ d : Fin 23, (2*Q-2+1 : ℕ) * (∫ g, occupationQuadratic Q (finiteFourMiddle Q (d.val+1))
        (fun i : Fin ((d.val+2)/2) => physicalFourCopyEnd Q
          (Certificate.copyLabel (D := d.val+1) i) (d.val+1) (by omega)
          (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) := by
  have hs : (∑ d : Fin 23, fourBodyRho (d.val+1) Q) ≤ uniformFourBodyRho Q := by
    rw [Fin.sum_univ_eq_sum_range (fun d => fourBodyRho (d+1) Q) 23]
    unfold uniformFourBodyRho
    rw [Finset.sum_range_succ' (fun D => fourBodyRho D Q) 23]
    exact le_add_of_nonneg_right (fourBodyRho_nonneg 0 Q)
  have hE : 0 ≤ sourceFockEnergy Q x :=
    Finset.sum_nonneg (fun p hp => occupationNormSq_nonneg Q _)
  calc
    _ ≤ -(24 * (∑ d : Fin 23, fourBodyRho (d.val+1) Q) * sourceFockEnergy Q x) :=
      neg_le_neg (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hE)
    _ = ∑ d : Fin 23, -(24 * fourBodyRho (d.val+1) Q * sourceFockEnergy Q x) := by
      rw [Finset.mul_sum,Finset.sum_mul,Finset.sum_neg_distrib]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      exact physical_fourBody_haar_transfer Q (d.val+1) hQ (by omega) (by omega) x

end Laughlin.Fock

end OAI
