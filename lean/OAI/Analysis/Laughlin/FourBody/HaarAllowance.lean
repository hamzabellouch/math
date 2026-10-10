import OAI.Analysis.Laughlin.Fock.OrbitIntegration
import OAI.Analysis.Laughlin.FourBody.PhysicalAllowance
import OAI.Analysis.Laughlin.Operators.LocalFourCardinality

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators

theorem physical_fourBody_haar_allowance (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (hQ : D+2 ≤ Q) (x : Space Q) :
    (2*Q-2+1 : ℕ) * (∫ g, occupationNormSq Q
      (physicalFourCopyEnd Q r D (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) ≤
      (Fintype.card (LocalFourIndex D) : ℝ) * sourceFockEnergy Q x := by
  have hi := integral_mono
    (linearMap_rotation_norm_integrable Q (physicalFourCopyEnd Q r D (by omega)) x)
    (integrable_finsetSum _ (fun (b : LocalFourIndex D) hb => linearMap_rotation_norm_integrable Q
      (sourcePairEnd Q b.val.1.val) x))
    (fun g => source_fourBody_normalized_allowance Q r D hr hor hQ (exteriorRotation Q g⁻¹ x))
  apply (mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ (2*Q-2+1 : ℕ))).trans_eq
  rw [integral_finsetSum _ (fun (b : LocalFourIndex D) hb => linearMap_rotation_norm_integrable Q _ x)]
  have hp (b : LocalFourIndex D) :
      (∫ g, occupationNormSq Q (sourcePairEnd Q b.val.1.val (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
        sourceFockEnergy Q x/(2*Q-2+1 : ℕ) :=
    physical_pair_norm_haar_real Q (by omega) ⟨b.val.1.val,by have := b.val.1.isLt; omega⟩ x
  simp_rw [hp]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hd : ((2*Q-2+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem physical_fourBody_haar_allowance_retained (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (hQ : 25 ≤ Q) (hD : D ≤ 23) (x : Space Q) :
    (2*Q-2+1 : ℕ) * (∫ g, occupationNormSq Q
      (physicalFourCopyEnd Q r D (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) ≤
      ((D+1)^2/4 : ℕ) * sourceFockEnergy Q x := by
  simpa only [localFourIndex_card_retained D hD] using
    physical_fourBody_haar_allowance Q r D hr hor (by omega) x

end Laughlin.Fock

end OAI
