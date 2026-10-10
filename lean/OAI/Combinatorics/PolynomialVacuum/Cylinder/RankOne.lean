import OAI.Combinatorics.PolynomialVacuum.Cylinder.LimitFactor
import OAI.Combinatorics.PolynomialVacuum.Cylinder.EmptyBoundary

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M : ℕ} [NeZero M]

theorem arcLimit_rank_one (inp out : ZMod M → Spin) :
    arcLimit inp out=arcLimit (fun _=>.zero) out*arcLimit inp (fun _=>.zero) := by
  have hz : lowerAmplitude (M:=M) (fun _=>.zero)*upperAmplitude (M:=M) (fun _=>.zero)=1 := by
    rw [← arcLimit_factor,arcLimit_empty]
  rw [arcLimit_factor,arcLimit_factor,arcLimit_factor]
  calc
    _ = (lowerAmplitude inp*upperAmplitude out)*1 := (mul_one _).symm
    _ = _ := by rw [← hz]; ring
end PolynomialVacuumCylinder
namespace PolynomialVacuumAlgebra
open Classical Filter PolynomialVacuumCylinder
open scoped Topology

noncomputable def physicalProjection (N : ℕ) : Matrix (Fin (N+1) → Spin) (Fin (N+1) → Spin) ℂ :=
  fun out inp=>arcLimit (cylinderState N inp) (cylinderState N out)

theorem physicalProjection_tendsto (N : ℕ) :
    Tendsto (fun H=>physicalTransfer (N+1) zeta^H) atTop (nhds (physicalProjection N)) := by
  apply tendsto_pi_nhds.mpr
  intro out
  apply tendsto_pi_nhds.mpr
  intro inp
  exact physicalTransfer_powers_tendsto N out inp

@[simp] theorem physicalProjection_empty (N : ℕ) :
    physicalProjection N (fun _=>.zero) (fun _=>.zero)=1 := arcLimit_empty

theorem physicalProjection_factor (N : ℕ) (out inp : Fin (N+1) → Spin) :
    physicalProjection N out inp=physicalProjection N out (fun _=>.zero)*physicalProjection N (fun _=>.zero) inp :=
  arcLimit_rank_one _ _

theorem physicalProjection_left_fixed (N : ℕ) :
    physicalTransfer (N+1) zeta*physicalProjection N=physicalProjection N := by
  have h:=(tendsto_const_nhds (x:=physicalTransfer (N+1) zeta)).mul (physicalProjection_tendsto N)
  have hc : Tendsto (fun H=>physicalTransfer (N+1) zeta^(H+1)) atTop (nhds (physicalProjection N)) :=
    (physicalProjection_tendsto N).comp (tendsto_add_atTop_nat 1)
  simp only [pow_succ'] at hc
  exact tendsto_nhds_unique h hc

theorem physicalProjection_right_fixed (N : ℕ) :
    physicalProjection N*physicalTransfer (N+1) zeta=physicalProjection N := by
  have h:=(physicalProjection_tendsto N).mul (tendsto_const_nhds (x:=physicalTransfer (N+1) zeta))
  have hc : Tendsto (fun H=>physicalTransfer (N+1) zeta^(H+1)) atTop (nhds (physicalProjection N)) :=
    (physicalProjection_tendsto N).comp (tendsto_add_atTop_nat 1)
  simp only [pow_succ] at hc
  exact tendsto_nhds_unique h hc

theorem physicalProjection_fixed_vector (N : ℕ) (v : (Fin (N+1) → Spin) → ℂ)
    (hv : (physicalTransfer (N+1) zeta).mulVec v=v) : (physicalProjection N).mulVec v=v := by
  have hh (H : ℕ) : (physicalTransfer (N+1) zeta^H).mulVec v=v := by
    induction H with
    | zero => simp
    | succ H ih => rw [pow_succ',← Matrix.mulVec_mulVec,ih,hv]
  have ht : Tendsto (fun H=>(physicalTransfer (N+1) zeta^H).mulVec v) atTop
      (nhds ((physicalProjection N).mulVec v)) := by
    apply tendsto_pi_nhds.mpr
    intro out
    exact tendsto_finsetSum _ (fun inp _=>(physicalTransfer_powers_tendsto N out inp).mul_const (v inp))
  simp only [hh] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem physicalProjection_idempotent (N : ℕ) : physicalProjection N*physicalProjection N=physicalProjection N := by
  ext out inp
  have hv : (physicalTransfer (N+1) zeta).mulVec (fun s=>physicalProjection N s inp)=(fun s=>physicalProjection N s inp) := by
    funext s
    exact congrFun (congrFun (physicalProjection_left_fixed N) s) inp
  exact congrFun (physicalProjection_fixed_vector N _ hv) out

theorem physicalPolynomialVector_normalized (N : ℕ) (s : Fin (N+1) → Spin) :
    physicalPolynomialVector (N+1) s=physicalProjection N s (fun _=>.zero)*
      physicalPolynomialVector (N+1) (fun _=>.zero) := by
  have hv : (physicalTransfer (N+1) zeta).mulVec (physicalPolynomialVector (N+1))=physicalPolynomialVector (N+1) :=
    funext (physicalPolynomialVector_eigen (N+1))
  have hp:=physicalProjection_fixed_vector N _ hv
  have h0:=congrFun hp (fun _=>Spin.zero)
  have hs:=congrFun hp s
  rw [Matrix.mulVec,dotProduct] at h0 hs
  have he : (∑ i, physicalProjection N s i * physicalPolynomialVector (N+1) i) =
      physicalProjection N s (fun _=>.zero) *
        (∑ i, physicalProjection N (fun _=>.zero) i * physicalPolynomialVector (N+1) i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [physicalProjection_factor N s i]
    ring
  rw [he] at hs
  rw [← h0]
  exact hs.symm
end PolynomialVacuumAlgebra

end OAI
