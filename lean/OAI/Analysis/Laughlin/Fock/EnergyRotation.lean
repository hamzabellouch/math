import OAI.Analysis.Laughlin.Fock.UnitaryFamilies
import OAI.Analysis.Laughlin.Pair.FockCovariance

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem sourceFockEnergy_eq_fin (Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    sourceFockEnergy Q x = ∑ p : Fin (2*Q-2+1), occupationNormSq Q (sourcePairEnd Q p.val x) := by
  unfold sourceFockEnergy
  rw [show 2*Q-1=2*Q-2+1 by omega]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

theorem sourceFockEnergy_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2) (x : Space Q) :
    sourceFockEnergy Q (exteriorRotation Q g x) = sourceFockEnergy Q x := by
  rw [sourceFockEnergy_eq_fin Q hQ,sourceFockEnergy_eq_fin Q hQ]
  simp_rw [sourcePairEnd_rotation Q hQ g]
  have hu := Matrix.mem_unitaryGroup_iff'.mp (sourceSpinRepresentation_unitary (2*Q-2) g)
  rw [Matrix.star_eq_conjTranspose] at hu
  rw [unitary_sum_occupationNormSq Q _ hu]
  simp only [exteriorRotation_norm]

theorem sourceFockHamiltonian_apply_fin (Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    sourceFockHamiltonian Q x = ∑ p : Fin (2*Q-2+1),
      sourcePairVector Q p.val * sourcePairEnd Q p.val x := by
  simp only [sourceFockHamiltonian,LinearMap.sum_apply,Module.End.mul_apply,sourcePairCreateEnd_mul]
  rw [show 2*Q-1=2*Q-2+1 by omega]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

theorem sourceFockHamiltonian_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2) (x : Space Q) :
    sourceFockHamiltonian Q (exteriorRotation Q g x) =
      exteriorRotation Q g (sourceFockHamiltonian Q x) := by
  rw [sourceFockHamiltonian_apply_fin Q hQ,sourceFockHamiltonian_apply_fin Q hQ]
  simp only [sourcePairEnd_rotation Q hQ g,map_sum,map_mul,sourcePairVector_rotation Q hQ,
    Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
