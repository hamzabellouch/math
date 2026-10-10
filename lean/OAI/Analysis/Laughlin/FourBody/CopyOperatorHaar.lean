import OAI.Analysis.Laughlin.FourBody.HaarTransfer
import OAI.Analysis.Laughlin.FourBody.HighestFock

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

noncomputable def fourCopyOperator (Q D : ℕ) (hQ : D+2 ≤ Q)
    (C : OddPairLabel D → OddPairLabel D → ℝ) : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ :=
  ∑ r, ∑ s, (C r s : ℂ) •
    (retainedFourInclusion Q D hQ r * (retainedFourInclusion Q D hQ s)ᴴ)

theorem linearMap_rotation_inner_integrable (Q : ℕ) (L R : Module.End ℂ (Space Q)) (x : Space Q) :
    Integrable (fun g : SourceSU2 => occupationInner Q
      (L (exteriorRotation Q g⁻¹ x)) (R (exteriorRotation Q g⁻¹ x))) sourceHaar := by
  apply Continuous.integrable_of_hasCompactSupport _ (isClosed_tsupport _).isCompact
  unfold occupationInner
  apply continuous_finsetSum
  intro A hA
  exact (linearMap_rotation_coordinate_continuous Q L x A).star.mul
    (linearMap_rotation_coordinate_continuous Q R x A)

theorem physical_fourCopyOperator_haar (Q D : ℕ) (hQ : D+2 ≤ Q)
    (C : OddPairLabel D → OddPairLabel D → ℝ) (x : Space Q) :
    ((4*Q-1-2*D : ℕ) : ℝ) * (∫ g, occupationQuadratic Q C
      (fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
        (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ C) x).re := by
  let L : OddPairLabel D → Module.End ℂ (Space Q) :=
    fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
  have hi (r s : OddPairLabel D) := linearMap_rotation_inner_integrable Q (L r) (L s) x
  have hisum : Integrable (fun g : SourceSU2 => ∑ r, ∑ s,
      (C r s : ℂ) * occupationInner Q (L r (exteriorRotation Q g⁻¹ x))
        (L s (exteriorRotation Q g⁻¹ x))) sourceHaar :=
    integrable_finsetSum _ (fun r hr => integrable_finsetSum _ (fun s hs => (hi r s).const_mul _))
  have hc : ((4*Q-1-2*D : ℕ) : ℂ) * (∫ g, ∑ r, ∑ s,
      (C r s : ℂ) * occupationInner Q (L r (exteriorRotation Q g⁻¹ x))
        (L s (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ C) x := by
    rw [integral_finsetSum _ (fun r hr => integrable_finsetSum _ (fun s hs => (hi r s).const_mul _))]
    simp_rw [integral_finsetSum _ (fun s hs => (hi _ s).const_mul _),integral_const_mul]
    simp only [fourCopyOperator,contractionForm_sum,contractionForm_smul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    calc
      _ = (C r s : ℂ) * (((4*Q-1-2*D : ℕ) : ℂ) * (∫ g, occupationInner Q
        (L r (exteriorRotation Q g⁻¹ x)) (L s (exteriorRotation Q g⁻¹ x)) ∂sourceHaar)) := by ring
      _ = _ := by rw [physicalFourCopyEnd_cross_haar Q D hQ r s]
  have hr := congrArg Complex.re hc
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at hr
  have hre := integral_re hisum
  change (∫ g, (∑ r, ∑ s, (C r s : ℂ) * occupationInner Q
    (L r (exteriorRotation Q g⁻¹ x)) (L s (exteriorRotation Q g⁻¹ x))).re ∂sourceHaar) =
    (∫ g, ∑ r, ∑ s, (C r s : ℂ) * occupationInner Q
      (L r (exteriorRotation Q g⁻¹ x)) (L s (exteriorRotation Q g⁻¹ x)) ∂sourceHaar).re at hre
  rw [← hre] at hr
  simpa only [occupationQuadratic,L,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    zero_mul,sub_zero] using hr

theorem physical_fourCopyOperator_transfer (Q D : ℕ) (hQ : 25 ≤ Q) (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23)
    (x : Space Q) :
    -(24*fourBodyRho D Q*sourceFockEnergy Q x) ≤
      (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
        (contractionForm Q (sourceFourFamilyEnd Q)
          (fourCopyOperator Q D (by omega) (finiteFourMiddle Q D)) x).re := by
  have h := physical_fourBody_haar_transfer Q D hQ hD₁ hD₂ x
  have he := physical_fourCopyOperator_haar Q D (by omega) (finiteFourMiddle Q D) x
  have hd : ((4*Q-1-2*D : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 4*Q-1-2*D ≠ 0 by omega)
  rw [← he]
  have hm : (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ))*((4*Q-1-2*D : ℕ) : ℝ) =
      ((2*Q-2+1 : ℕ) : ℝ) := by field_simp
  rw [← mul_assoc,hm]
  exact h

end Laughlin.Fock

end OAI
