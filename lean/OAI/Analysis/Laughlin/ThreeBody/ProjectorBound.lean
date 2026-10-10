import OAI.Analysis.Laughlin.ThreeBody.HighestFock

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem physical_threeBody_projector_nonneg (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (x : Space Q) :
    0 ≤ (contractionForm Q (sourceThreeEnd Q)
      ((threeSpinProjector Q hQ z).map Complex.ofReal) x).re := by
  rw [← sourceThreeHighestEnd_haar Q hQ z]
  exact mul_nonneg (by positivity) (integral_nonneg (fun g => occupationNormSq_nonneg Q _))

theorem physical_threeBody_projector_bound (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (x : Space Q) :
    (contractionForm Q (sourceThreeEnd Q)
      ((threeSpinProjector Q hQ z).map Complex.ofReal) x).re ≤
      ((coupledWeight Q z.val+1 : ℕ) / (2*Q-2+1 : ℕ) : ℝ) *
        (z.val+1 : ℕ) * sourceFockEnergy Q x := by
  rw [← sourceThreeHighestEnd_haar Q hQ z]
  have hi := integral_mono
    (linearMap_rotation_norm_integrable Q (sourceThreeHighestEnd Q z.val hQ (by omega)) x)
    (integrable_finsetSum _ (fun (p : Fin (z.val+1)) hp =>
      linearMap_rotation_norm_integrable Q (sourcePairEnd Q p.val) x))
    (fun g => sourceThreeHighestEnd_norm_bound Q z.val hQ (by omega) (exteriorRotation Q g⁻¹ x))
  apply (mul_le_mul_of_nonneg_left hi
    (by positivity : (0 : ℝ) ≤ (coupledWeight Q z.val+1 : ℕ))).trans_eq
  rw [integral_finsetSum _ (fun (p : Fin (z.val+1)) hp =>
    linearMap_rotation_norm_integrable Q (sourcePairEnd Q p.val) x)]
  have hp (p : Fin (z.val+1)) :
      (∫ g, occupationNormSq Q (sourcePairEnd Q p.val (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
        sourceFockEnergy Q x/(2*Q-2+1 : ℕ) :=
    physical_pair_norm_haar_real Q (by omega) ⟨p.val,by have := p.isLt; have := z.isLt; omega⟩ x
  simp_rw [hp]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end Laughlin.Fock

end OAI
