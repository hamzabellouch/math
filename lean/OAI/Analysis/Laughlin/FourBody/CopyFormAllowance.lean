import OAI.Analysis.Laughlin.FourBody.CopyAlgebra
import OAI.Analysis.Laughlin.FourBody.TotalAllowance

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators Matrix

private theorem scaled_sum_of_haar_identity {ι : Type*} [Fintype ι]
    (a d t : ℝ) (f : ι → ℝ) (hd : d ≠ 0) (h : d * ∑ i, f i = t) :
    (a / d) * t = ∑ i, a * f i := by
  rw [← h, ← Finset.mul_sum]
  field_simp

theorem fourCopyForm_allowance_identity (Q D : ℕ) (hQ : D+2 ≤ Q) (x : Space Q) :
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (∑ r : OddPairLabel D, (contractionForm Q (sourceFourFamilyEnd Q)
        (retainedFourInclusion Q D hQ r*(retainedFourInclusion Q D hQ r)ᴴ) x).re) =
      ∑ r : OddPairLabel D, ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, occupationNormSq Q
        (physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
          (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) := by
  classical
  have hd : ((4*Q-1-2*D : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  have h := physical_fourCopyOperator_haar Q D hQ (Matrix.diagonal (fun _ : OddPairLabel D => (1 : ℝ))) x
  rw [fourCopyOperator_diagonal] at h
  simp only [Complex.ofReal_one,one_smul,contractionForm_sum,Complex.re_sum] at h
  have he (g : SourceSU2) : occupationQuadratic Q (Matrix.diagonal (fun _ : OddPairLabel D => (1 : ℝ)))
      (fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega) (exteriorRotation Q g⁻¹ x)) =
      ∑ r : OddPairLabel D, occupationNormSq Q
        (physicalFourCopyEnd Q (oddPairDeficit r) D (by omega) (exteriorRotation Q g⁻¹ x)) := by
    simp only [occupationQuadratic,Matrix.diagonal_apply,apply_ite,Complex.ofReal_one,
      Complex.ofReal_zero,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,
      ite_true,occupationInner_self,Complex.re_sum,Complex.ofReal_re]
  simp_rw [he] at h
  rw [integral_finsetSum _ (fun (r : OddPairLabel D) hr => linearMap_rotation_norm_integrable Q
    (physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)) x)] at h
  exact scaled_sum_of_haar_identity _ _ _ _ hd h

noncomputable def retainedFourAllowance (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) : ℝ :=
  ∑ d : Fin 23, (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*(d.val+1) : ℕ) : ℝ)) *
    (∑ r : OddPairLabel (d.val+1), (contractionForm Q (sourceFourFamilyEnd Q)
      (retainedFourInclusion Q (d.val+1) (by omega) r*
        (retainedFourInclusion Q (d.val+1) (by omega) r)ᴴ) x).re)

theorem retainedFourAllowance_bound (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    retainedFourAllowance Q hQ x ≤ 10946*sourceFockEnergy Q x := by
  unfold retainedFourAllowance
  simp_rw [fourCopyForm_allowance_identity]
  exact physical_fourBody_total_haar_allowance Q hQ x

end Laughlin.Fock

end OAI
