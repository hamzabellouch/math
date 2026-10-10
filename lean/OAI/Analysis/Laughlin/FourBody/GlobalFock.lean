import OAI.Analysis.Laughlin.FourBody.GlobalHaar

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem physical_fourBody_global_Fock_haar (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (∫ g, contractionForm Q (sourceFourFamilyEnd Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
    ∑ d : Fin 23, (1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) *
      contractionForm Q (sourceFourFamilyEnd Q)
        (fourCopyOperator Q (d.val+1) (by omega)
          (fun r s => physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s))) x := by
  rw [contractionForm_haar Q (fourBodySpinRepresentation Q)
    (fourBodySpinRepresentation_inv Q) (fourBodySpinRepresentation_continuous Q)
    _ (sourceFourFamilyEnd_rotation Q (by omega)),physicalFourBodyHaar_retained_sum Q hQ,
    contractionForm_sum]
  simp only [contractionForm_smul]

noncomputable def sourceA4Form (Q : ℕ) (x : Space Q) : ℝ :=
  ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, contractionForm Q (sourceFourFamilyEnd Q)
    ((physicalFourBodyMatrix Q).map Complex.ofReal) (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re

theorem sourceA4Form_retained (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceA4Form Q x = ∑ d : Fin 23,
      (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*(d.val+1) : ℕ) : ℝ)) *
        (contractionForm Q (sourceFourFamilyEnd Q)
          (fourCopyOperator Q (d.val+1) (by omega)
            (fun r s => physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s))) x).re := by
  rw [sourceA4Form,physical_fourBody_global_Fock_haar Q hQ x,Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have he : (1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) =
      ((1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

end Laughlin.Fock

end OAI
