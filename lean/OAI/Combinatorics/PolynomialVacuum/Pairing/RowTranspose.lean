import OAI.Combinatorics.PolynomialVacuum.Pairing.RowDuality

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

def dualAuxEquiv (N : ℕ) : (Fin (N+1) → Spin) ≃ (Fin (N+1) → Spin) where
  toFun:=dualAux
  invFun s j:=oppositeSpin (s (j-1))
  left_inv s:=by funext j; simp [dualAux]
  right_inv s:=by funext j; simp [dualAux]
def dualInternalEquiv (N : ℕ) : (Fin (N+1) → Spin) ≃ (Fin (N+1) → Spin) :=
  Equiv.piCongrRight (fun _=>oppositeSpinEquiv)

def rowDualityEquiv (N : ℕ) : ((Fin (N+1) → Spin) × (Fin (N+1) → Spin)) ≃
    ((Fin (N+1) → Spin) × (Fin (N+1) → Spin)) :=
  (Equiv.prodComm _ _).trans ((dualAuxEquiv N).prodCongr (dualInternalEquiv N))

@[simp] theorem last_add_one (N : ℕ) : (Fin.last N+1 : Fin (N+1))=0 := by
  apply Fin.ext
  simp [Fin.add_def]

theorem twisted_row_weight_dual (N : ℕ) (κ : ℂ) (hκ : κ≠0) (out inp a k : Fin (N+1) → Spin) :
    κ^charge (a (Fin.last N))*triangleRowWeight out inp a k=
      κ^charge (out 0)*((κ⁻¹)^charge (dualAux k (Fin.last N))*
        triangleRowWeight inp (shiftForward out) (dualAux k) (dualInternal a)) := by
  rw [← triangleRowWeight_dual]
  by_cases hw : triangleRowWeight out inp a k=0
  · simp [hw]
  · have hh:=triangleRowWeight_zero_ice out inp a k hw
    simp only [dualAux,last_add_one,charge_oppositeSpin,inv_zpow,zpow_neg,inv_inv]
    rw [hh,zpow_add₀ hκ]
    ring

theorem physicalTransfer_transpose_rotation (N : ℕ) (κ : ℂ) (hκ : κ≠0) (out inp : Fin (N+1) → Spin) :
    physicalTransfer (N+1) κ out inp=
      κ^charge (out 0)*physicalTransfer (N+1) κ⁻¹ inp (shiftForward out) := by
  simp only [physicalTransfer_periodic,row_triangle_weight]
  rw [← Fintype.sum_prod_type (f:=fun ak : (Fin (N+1) → Spin) × (Fin (N+1) → Spin)=>κ^charge (ak.1 (Fin.last N))*triangleRowWeight out inp ak.1 ak.2),
    ← Fintype.sum_prod_type (f:=fun ak : (Fin (N+1) → Spin) × (Fin (N+1) → Spin)=>(κ⁻¹)^charge (ak.1 (Fin.last N))*triangleRowWeight inp (shiftForward out) ak.1 ak.2)]
  rw [← Equiv.sum_comp (rowDualityEquiv N) (fun ak=>
    (κ⁻¹)^charge (ak.1 (Fin.last N))*triangleRowWeight inp (shiftForward out) ak.1 ak.2)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ak _
  exact twisted_row_weight_dual N κ hκ out inp ak.1 ak.2

end PolynomialVacuumAlgebra

end OAI
