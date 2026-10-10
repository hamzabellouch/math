import OAI.Combinatorics.PolynomialVacuum.Pairing.RowCyclic
import OAI.Combinatorics.PolynomialVacuum.Algebra.AnalyticNormalization

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical Filter PolynomialVacuumCylinder
open scoped Topology

theorem physicalTransfer_power_column_cyclic (N H : ℕ) (κ : ℂ) (hκ : κ≠0) :
    ∀s,κ^charge (s 0)*(physicalTransfer (N+1) κ^H) (shiftForward s) (fun _=>.zero)=
      (physicalTransfer (N+1) κ^H) s (fun _=>.zero) := by
  induction H with
  | zero =>
    intro s
    simp only [pow_zero,Matrix.one_apply]
    by_cases hs : s=(fun _=>Spin.zero)
    · subst s
      have hz : shiftForward (fun _ : Fin (N+1)=>Spin.zero)=(fun _=>Spin.zero) := rfl
      simp [hz,charge]
    · have hh : shiftForward s≠(fun _=>Spin.zero) := by
        intro h
        apply hs
        exact (shiftForwardEquiv N).injective h
      simp [hs,hh]
  | succ H ih =>
    simpa only [pow_succ',Matrix.mul_apply,Matrix.mulVec,dotProduct] using
      physicalTransfer_mulVec_cyclic N κ hκ (fun s=>(physicalTransfer (N+1) κ^H) s (fun _=>.zero)) ih

 

theorem physicalTransfer_upper_lower (N H : ℕ) (κ : ℂ) (hκ : κ≠0)
    (s : Fin (N+1) → Spin) :
    (physicalTransfer (N+1) κ⁻¹^H) (fun _=>.zero) s=
      (physicalTransfer (N+1) κ^H) s (fun _=>.zero) := by
  induction H generalizing s with
  | zero => simp only [pow_zero,Matrix.one_apply]; split_ifs <;> simp_all
  | succ H ih =>
    have hv := physicalTransfer_dual_mulVec N κ hκ
      (fun s=>(physicalTransfer (N+1) κ^H) s (fun _=>.zero))
      (physicalTransfer_power_column_cyclic N H κ hκ)
    rw [pow_succ (physicalTransfer (N+1) κ⁻¹),pow_succ' (physicalTransfer (N+1) κ)]
    simp only [Matrix.mul_apply]
    simp_rw [ih]
    simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,mul_comm] using congrFun hv s

theorem physicalUpper_tendsto (N : ℕ) (s : Fin (N+1) → Spin) :
    Tendsto (fun H=>(physicalTransfer (N+1) zeta⁻¹^H) (fun _=>.zero) s) atTop
      (nhds (AnalyticVacuum.normalizedVacuum (N+1) (fun _=>1) s)) := by
  simp_rw [physicalTransfer_upper_lower N _ zeta (by simp [zeta_eq_I])]
  rw [AnalyticVacuum.normalizedVacuum_homogeneous]
  exact physicalTransfer_powers_tendsto N s (fun _=>.zero)

end PolynomialVacuumAlgebra

end OAI
