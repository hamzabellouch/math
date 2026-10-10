import OAI.Analysis.Laughlin.Fock.OrbitIntegration
import OAI.Analysis.Laughlin.Fock.RankOneHaar
import OAI.Analysis.Laughlin.Operators.WeightedOccupationNorm
import OAI.Analysis.Laughlin.ThreeBody.FockHaar

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

noncomputable def sourceThreeHighestEnd (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    Module.End ℂ (Space Q) :=
  ∑ p : Fin (z+1), (highestUnit (2*Q-2) Q z p.val : ℂ) •
    sourceThreeEnd Q (weightSliceIndex (2*Q-2) Q z (by omega) hz p)

theorem threeCoupledInclusion_highest (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (i : PairOrbitalIndex Q) :
    threeCoupledInclusion Q hQ z i 0 = (coupledHighest Q z.val hQ (by omega) i : ℂ) := by
  have hn : vectorNormSq (coupledHighest Q z.val hQ (by omega))=1 :=
    coupledHighest_norm Q z.val hQ (by omega)
  simp only [threeCoupledInclusion,normalizedCoupledDescendant,coupledDescendant,
    Fin.val_zero,pow_zero,Matrix.one_mulVec,hn,Real.sqrt_one,inv_one,one_smul]

theorem sourceThreeHighestEnd_column (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (x : Space Q) :
    (∑ i, star (threeCoupledInclusion Q hQ z i 0) • sourceThreeEnd Q i x) =
      sourceThreeHighestEnd Q z.val hQ (by omega) x := by
  simp only [threeCoupledInclusion_highest,coupledHighest,extendWeightSlice,
    Complex.ofReal_sum,star_sum,Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [apply_ite,Complex.ofReal_zero,star_zero,Complex.star_def,Complex.conj_ofReal,
    ite_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,sourceThreeHighestEnd,
    LinearMap.sum_apply,LinearMap.smul_apply]

theorem sourceThreeHighestEnd_norm_bound (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (x : Space Q) :
    occupationNormSq Q (sourceThreeHighestEnd Q z hQ hz x) ≤
      ∑ p : Fin (z+1), occupationNormSq Q (sourcePairEnd Q p.val x) := by
  have hn : (∑ p : Fin (z+1), (highestUnit (2*Q-2) Q z p.val)^2)=1 := by
    rw [Fin.sum_univ_eq_sum_range (fun p => (highestUnit (2*Q-2) Q z p)^2) (z+1)]
    exact highestUnit_norm (2*Q-2) Q z (by omega) hz
  simp only [sourceThreeHighestEnd,LinearMap.sum_apply,LinearMap.smul_apply]
  apply (normalized_occupation_sum_bound Q _ _ hn).trans
  apply Finset.sum_le_sum
  intro p hp
  exact annihilate_normSq_le Q _ (sourcePairEnd Q p.val x)

theorem sourceThreeHighestEnd_haar (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (x : Space Q) :
    (coupledWeight Q z.val+1 : ℕ) * (∫ g, occupationNormSq Q
      (sourceThreeHighestEnd Q z.val hQ (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      (contractionForm Q (sourceThreeEnd Q) ((threeSpinProjector Q hQ z).map Complex.ofReal) x).re := by
  have h := physical_family_spin_norm_haar Q (threeBodySpinRepresentation Q)
    (threeBodySpinRepresentation_inv Q) (threeBodySpinRepresentation_continuous Q)
    (sourceThreeEnd Q) (sourceThreeEnd_rotation Q (by omega))
    (coupledWeight Q z.val) (threeCoupledInclusion Q hQ z)
    (threeCoupledInclusion_SU2 Q hQ z) 0 x
  simp_rw [sourceThreeHighestEnd_column] at h
  rw [← threeSpinProjector_complex_factor,integral_complex_ofReal] at h
  have hh := congrArg Complex.re h
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,Complex.natCast_im,zero_mul,mul_zero,sub_zero] using hh

end Laughlin.Fock

end OAI
