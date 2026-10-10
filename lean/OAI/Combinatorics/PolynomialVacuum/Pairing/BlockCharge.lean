import OAI.Combinatorics.PolynomialVacuum.Pairing.MarkedRows

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder

theorem cylinderBlockCharge_coordinate (N k : ℕ) (hk : k≤N+1) (s : Fin (N+1) → Spin) :
    cylinderBlockCharge k (cylinderState N s)=∑j : Fin k,charge (s ⟨j.val,j.isLt.trans_le hk⟩) := by
  apply Finset.sum_congr rfl
  intro j _
  have hj : -(j.val : ZMod (N+1))=rowCoordinate N ⟨j.val,j.isLt.trans_le hk⟩ := by
    change -(j.val : ZMod (N+1)) = -(ZMod.finEquiv (N+1) ⟨j.val,j.isLt.trans_le hk⟩)
    congr 1
    apply ZMod.val_injective
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (j.isLt.trans_le hk)
  rw [hj,cylinderState_coordinate]

theorem physicalCutDiagonal_coordinate (N k : ℕ) (hk : k≤N+1) (κ : ℂ) (s : Fin (N+1) → Spin) :
    physicalCutDiagonal N k κ s=(κ/zeta)^(∑j : Fin k,charge (s ⟨j.val,j.isLt.trans_le hk⟩)) := by
  rw [physicalCutDiagonal,cylinderBlockCharge_coordinate N k hk]

 
theorem physical_limit_is_contraction (n : ℕ) (hn : 1≤n) (κ : ℂ) :
    (∑s : Fin (2*n-1+1) → Spin,
      AnalyticVacuum.normalizedVacuum (2*n-1+1) (fun _=>1) s*physicalCutDiagonal (2*n-1) n κ s*
        AnalyticVacuum.normalizedVacuum (2*n-1+1) (fun _=>1) s)=
      analyticHomogeneousContraction AnalyticVacuum.normalizedVacuum n κ := by
  have hw : 2*n-1+1=2*n := by omega
  simp_rw [physicalCutDiagonal_coordinate (2*n-1) n (by omega) κ]
  let f (M : ℕ) (hM : n≤M) : ℂ :=
    ∑s : Fin M → Spin,AnalyticVacuum.normalizedVacuum M (fun _=>1) s*
      (κ/zeta)^(∑j : Fin n,charge (s ⟨j.val,j.isLt.trans_le hM⟩))*
        AnalyticVacuum.normalizedVacuum M (fun _=>1) s
  change f (2*n-1+1) (by omega)=f (2*n) (by omega)
  congr 1
  omega

end PolynomialVacuumAlgebra

end OAI
