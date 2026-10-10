import OAI.Combinatorics.PolynomialVacuum.Cylinder.RankOne

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

noncomputable def emptyMatrix (N : ℕ) : Matrix (Fin N → Spin) (Fin N → Spin) ℂ :=
  Matrix.single (fun _=>.zero) (fun _=>.zero) 1

theorem emptyMatrix_mulVec (N : ℕ) (v : (Fin N → Spin) → ℂ) :
    (emptyMatrix N).mulVec v=Pi.single (fun _=>.zero) (v (fun _=>.zero)) := by
  simp [emptyMatrix,Matrix.single_mulVec,Pi.single]

theorem physical_resolvent_isUnit (N : ℕ) (d : ℂ) (hd : d≠0) :
    IsUnit (d • (1-physicalTransfer (N+1) zeta)+emptyMatrix (N+1)) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  rw [← Matrix.coe_mulVecLin]
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change (d • (1-physicalTransfer (N+1) zeta)+emptyMatrix (N+1)).mulVec v=0 at hv
  have hp:=congrArg (physicalProjection N).mulVec hv
  rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,emptyMatrix_mulVec] at hv
  have hpv : (physicalProjection N).mulVec ((physicalTransfer (N+1) zeta).mulVec v)=
      (physicalProjection N).mulVec v := by
    rw [Matrix.mulVec_mulVec,physicalProjection_right_fixed]
  rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,emptyMatrix_mulVec,
    Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_sub,hpv,sub_self,smul_zero,zero_add,Matrix.mulVec_zero] at hp
  have h0:=congrFun hp (fun _=>.zero)
  simp [Matrix.mulVec,dotProduct,Pi.single_apply] at h0
  have ht : (physicalTransfer (N+1) zeta).mulVec v=v := by
    rw [h0,Pi.single_zero,add_zero] at hv
    have he : v-(physicalTransfer (N+1) zeta).mulVec v=0 := (smul_eq_zero.mp hv).resolve_left hd
    exact (sub_eq_zero.mp he).symm
  have he:=physicalProjection_fixed_vector N v ht
  funext s
  have hh:=congrFun he s
  change (∑ i,physicalProjection N s i*v i)=v s at hh
  have hz:=congrFun he (fun _=>.zero)
  change (∑ i,physicalProjection N (fun _=>.zero) i*v i)=v (fun _=>.zero) at hz
  have hf : (∑ i,physicalProjection N s i*v i)=physicalProjection N s (fun _=>.zero)*
      (∑ i,physicalProjection N (fun _=>.zero) i*v i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [physicalProjection_factor N s i]
    ring
  rw [hf,hz,h0,mul_zero] at hh
  exact hh.symm
end PolynomialVacuumAlgebra

end OAI
