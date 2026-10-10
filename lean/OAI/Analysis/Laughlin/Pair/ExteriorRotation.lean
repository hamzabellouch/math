import OAI.Analysis.Laughlin.Exterior.SpinUnitary
import OAI.Analysis.Laughlin.Fock.PairNormalization
import OAI.Analysis.Laughlin.Operators.PhysicalPairRotation

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix Kronecker

noncomputable def pairExterior (Q : ℕ) (v : Spin.SpinIndex Q Q → ℂ) : Space Q :=
  ∑ i, v i • create i.1 (create i.2 (1 : Space Q))

theorem exteriorRotation_pair_basis (Q : ℕ) (g : SourceSU2) (i j : Fin (Q+1)) :
    exteriorRotation Q g (create i (create j (1 : Space Q))) =
      ∑ k : Spin.SpinIndex Q Q, (sourceSpinRepresentation Q g k.1 i * sourceSpinRepresentation Q g k.2 j) •
        create k.1 (create k.2 (1 : Space Q)) := by
  rw [create_exteriorRotation,create_exteriorRotation]
  simp only [map_one,map_sum,map_smul,Finset.smul_sum,smul_smul,Fintype.sum_prod_type]

theorem pairExterior_rotation (Q : ℕ) (g : SourceSU2) (v : Spin.SpinIndex Q Q → ℂ) :
    exteriorRotation Q g (pairExterior Q v) =
      pairExterior Q ((sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) *ᵥ v) := by
  simp only [pairExterior,map_sum,map_smul,exteriorRotation_pair_basis,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec,dotProduct,Matrix.kroneckerMap,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pairExterior_sum {I : Type*} [Fintype I] (Q : ℕ) (v : I → Spin.SpinIndex Q Q → ℂ) :
    pairExterior Q (∑ a, v a) = ∑ a, pairExterior Q (v a) := by
  simp only [pairExterior,Finset.sum_apply,Finset.sum_smul]
  rw [Finset.sum_comm]

theorem pairExterior_smul (Q : ℕ) (c : ℂ) (v : Spin.SpinIndex Q Q → ℂ) :
    pairExterior Q (c • v) = c • pairExterior Q v := by
  simp only [pairExterior,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]

theorem sourcePairVector_pairExterior (Q p : ℕ) :
    sourcePairVector Q p = (Real.sqrt 2 : ℂ)⁻¹ •
      pairExterior Q (fun i => (pairCoefficient Q p i.1 i.2 : ℂ)) := by
  simp only [sourcePairVector,pairExterior,Fintype.sum_prod_type,Finset.smul_sum,smul_smul,
    div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv,mul_comm]

theorem sourcePairVector_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
    (p : Fin (2*Q-2+1)) :
    exteriorRotation Q g (sourcePairVector Q p.val) =
      ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g q p • sourcePairVector Q q.val := by
  have hc : ((sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) *ᵥ
      (fun i => (pairCoefficient Q p.val i.1 i.2 : ℂ))) =
      ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g q p •
        (fun i : Spin.SpinIndex Q Q => (pairCoefficient Q q.val i.1 i.2 : ℂ)) := by
    funext i
    have h := congrFun (congrFun (physicalPairInclusion_SU2 Q hQ g) i) p
    simpa only [physicalPairInclusion,Spin.pairInclusion,Matrix.map_apply,Matrix.mul_apply,
      Matrix.mulVec,dotProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using h
  rw [sourcePairVector_pairExterior,map_smul,pairExterior_rotation,hc,pairExterior_sum]
  simp only [pairExterior_smul,Finset.smul_sum,sourcePairVector_pairExterior]
  apply Finset.sum_congr rfl
  intro q hq
  exact smul_comm _ _ _

end Laughlin.Fock

end OAI
