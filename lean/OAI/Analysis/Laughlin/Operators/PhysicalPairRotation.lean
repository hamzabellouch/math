import OAI.Analysis.Laughlin.Pair.LadderIntertwining
import OAI.Analysis.Laughlin.Spin.LadderGroupIntertwining

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix Kronecker

noncomputable def physicalPairInclusion (Q : ℕ) := (Spin.pairInclusion Q).map Complex.ofReal

theorem physicalPairInclusion_SU2 (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2) :
    (sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g)*physicalPairInclusion Q =
      physicalPairInclusion Q*sourceSpinRepresentation (2*Q-2) g := by
  apply ladder_intertwiner_SU2 Q Q 1 (2*Q-2) (by omega)
  · intro i n hi
    have hn : i.1.val+i.2.val ≠ n.val+1 := by omega
    simp [physicalPairInclusion,Spin.pairInclusion,pairCoefficient,hn]
  · ext i n
    have h := congrArg Complex.ofReal (congrFun (congrFun (Spin.pairInclusion_raising Q hQ) i) n)
    simpa [physicalPairInclusion,totalRaiseComplex,spinRaiseComplex,Matrix.mul_apply] using h
  · ext i n
    have h := congrArg Complex.ofReal (congrFun (congrFun (Spin.pairInclusion_lowering Q hQ) i) n)
    simpa [physicalPairInclusion,totalRaiseComplex,spinRaiseComplex,Matrix.mul_apply,Matrix.transpose_apply] using h

theorem physicalPairInclusion_isometry (Q : ℕ) (hQ : 2 ≤ Q) :
    (physicalPairInclusion Q)ᴴ*physicalPairInclusion Q=1 := by
  ext p q
  have h := congrArg Complex.ofReal (congrFun (congrFun (Spin.pairInclusion_isometry Q hQ) p) q)
  simpa [physicalPairInclusion,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply,
    Matrix.one_apply,apply_ite] using h

theorem physicalPairProjector_SU2 (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2) :
    (sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g)*
      (physicalPairInclusion Q*(physicalPairInclusion Q)ᴴ) =
      (physicalPairInclusion Q*(physicalPairInclusion Q)ᴴ)*
        (sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) := by
  have h := physicalPairInclusion_SU2 Q hQ g
  have hi := physicalPairInclusion_SU2 Q hQ g⁻¹
  have hinv (A : ℕ) : (sourceSpinRepresentation A g⁻¹)ᴴ=sourceSpinRepresentation A g := by
    have hu := Matrix.mem_unitaryGroup_iff.mp (sourceSpinRepresentation_unitary A g)
    rw [Matrix.star_eq_conjTranspose] at hu
    have hm : sourceSpinRepresentation A g⁻¹*sourceSpinRepresentation A g=1 := by
      rw [← map_mul,inv_mul_cancel,map_one]
    have he : sourceSpinRepresentation A g⁻¹=(sourceSpinRepresentation A g)ᴴ := by
      calc
        _ = sourceSpinRepresentation A g⁻¹*1 := by rw [Matrix.mul_one]
        _ = sourceSpinRepresentation A g⁻¹*(sourceSpinRepresentation A g*(sourceSpinRepresentation A g)ᴴ) := by rw [hu]
        _ = (sourceSpinRepresentation A g⁻¹*sourceSpinRepresentation A g)*(sourceSpinRepresentation A g)ᴴ := by rw [Matrix.mul_assoc]
        _ = _ := by rw [hm,Matrix.one_mul]
    rw [he,Matrix.conjTranspose_conjTranspose]
  have hs := hinv Q
  have hj := hinv (2*Q-2)
  have ht := congrArg Matrix.conjTranspose hi
  have hk : (sourceSpinRepresentation Q g⁻¹ ⊗ₖ sourceSpinRepresentation Q g⁻¹)ᴴ =
      sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g := by
    ext i j
    simp only [Matrix.conjTranspose_apply,Matrix.kroneckerMap,Matrix.of_apply]
    simpa only [Matrix.conjTranspose_apply,star_mul,mul_comm] using
      congrArg₂ (·*·) (congrFun (congrFun hs i.1) j.1) (congrFun (congrFun hs i.2) j.2)
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hk,hj] at ht
  rw [← Matrix.mul_assoc,h,Matrix.mul_assoc,← ht,← Matrix.mul_assoc]

end Laughlin.Rotation

end OAI
