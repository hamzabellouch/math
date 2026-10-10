import OAI.Combinatorics.PolynomialVacuum.Pairing.RowTranspose

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

def shiftForwardEquiv (N : ℕ) : (Fin (N+1) → Spin) ≃ (Fin (N+1) → Spin) where
  toFun:=shiftForward
  invFun s j:=s (j-1)
  left_inv s:=by funext j; simp [shiftForward]
  right_inv s:=by funext j; simp [shiftForward]

theorem triangleRowWeight_shift (N : ℕ) (out inp a k : Fin (N+1) → Spin) :
    triangleRowWeight (shiftForward out) (shiftForward inp) (shiftForward a) (shiftForward k)=
      triangleRowWeight out inp a k := by
  unfold triangleRowWeight shiftForward
  simpa only [Equiv.coe_addRight,add_sub_cancel_right,sub_add_cancel] using Equiv.prod_comp
    (Equiv.addRight (1 : Fin (N+1))) (fun j=>triangleUp (k j) (inp j) (a j)*triangleDown (k j) (out j) (a (j-1)))

theorem triangleRowWeight_ice_up (N : ℕ) (out inp a k : Fin (N+1) → Spin)
    (hw : triangleRowWeight out inp a k≠0) : charge (a 0)=charge (k 0)+charge (inp 0) := by
  have hu := (mul_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hw) 0 (Finset.mem_univ _))).1
  unfold triangleUp arrowVertexWeight at hu
  split_ifs at hu with hc
  · exact (up_ice _ _ _).mp hc
  · exact (hu rfl).elim

theorem twisted_shift_weight (N : ℕ) (κ : ℂ) (hκ : κ≠0) (out inp a k : Fin (N+1) → Spin) :
    κ^charge (out 0)*(κ^charge (shiftForward a (Fin.last N))*
      triangleRowWeight (shiftForward out) (shiftForward inp) (shiftForward a) (shiftForward k))=
    κ^charge (inp 0)*(κ^charge (a (Fin.last N))*triangleRowWeight out inp a k) := by
  rw [triangleRowWeight_shift]
  simp only [shiftForward,last_add_one]
  by_cases hw : triangleRowWeight out inp a k=0
  · simp [hw]
  · have hu:=triangleRowWeight_ice_up N out inp a k hw
    have hd:=triangleRowWeight_zero_ice out inp a k hw
    rw [← mul_assoc,← zpow_add₀ hκ,← mul_assoc,← zpow_add₀ hκ]
    congr 2
    omega

theorem physicalTransfer_cyclic (N : ℕ) (κ : ℂ) (hκ : κ≠0) (out inp : Fin (N+1) → Spin) :
    κ^charge (out 0)*physicalTransfer (N+1) κ (shiftForward out) (shiftForward inp)=
      κ^charge (inp 0)*physicalTransfer (N+1) κ out inp := by
  simp only [physicalTransfer_periodic,row_triangle_weight]
  let f : ((Fin (N+1) → Spin) × (Fin (N+1) → Spin)) → ℂ:=fun ak=>κ^charge (ak.1 (Fin.last N))*triangleRowWeight out inp ak.1 ak.2
  let g : ((Fin (N+1) → Spin) × (Fin (N+1) → Spin)) → ℂ:=fun ak=>κ^charge (ak.1 (Fin.last N))*triangleRowWeight (shiftForward out) (shiftForward inp) ak.1 ak.2
  change κ^charge (out 0)*(∑a,∑k,g (a,k))=κ^charge (inp 0)*(∑a,∑k,f (a,k))
  rw [← Fintype.sum_prod_type (f:=f),← Fintype.sum_prod_type (f:=g),
    ← Equiv.sum_comp ((shiftForwardEquiv N).prodCongr (shiftForwardEquiv N)) g]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ak _
  exact twisted_shift_weight N κ hκ out inp ak.1 ak.2

 
theorem physicalTransfer_mulVec_cyclic (N : ℕ) (κ : ℂ) (hκ : κ≠0)
    (v : (Fin (N+1) → Spin) → ℂ) (hv : ∀s,κ^charge (s 0)*v (shiftForward s)=v s) :
    ∀s,κ^charge (s 0)*(physicalTransfer (N+1) κ).mulVec v (shiftForward s)=
      (physicalTransfer (N+1) κ).mulVec v s := by
  intro s
  simp only [Matrix.mulVec,dotProduct]
  rw [← Equiv.sum_comp (shiftForwardEquiv N) (fun r=>physicalTransfer (N+1) κ (shiftForward s) r*v r),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  change κ^charge (s 0)*(physicalTransfer (N+1) κ (shiftForward s) (shiftForward r)*v (shiftForward r))=_
  rw [← mul_assoc,physicalTransfer_cyclic N κ hκ]
  calc
    _ = physicalTransfer (N+1) κ s r*(κ^charge (r 0)*v (shiftForward r)) := by ring
    _ = _ := by rw [hv]

 
theorem physicalTransfer_dual_mulVec (N : ℕ) (κ : ℂ) (hκ : κ≠0)
    (v : (Fin (N+1) → Spin) → ℂ) (hv : ∀s,κ^charge (s 0)*v (shiftForward s)=v s) :
    (physicalTransfer (N+1) κ⁻¹).transpose.mulVec v=(physicalTransfer (N+1) κ).mulVec v := by
  have hc:=physicalTransfer_mulVec_cyclic N κ hκ v hv
  funext s
  obtain ⟨r,rfl⟩ := (shiftForwardEquiv N).surjective s
  apply mul_left_cancel₀ (zpow_ne_zero (charge (r 0)) hκ)
  change κ^charge (r 0)*(physicalTransfer (N+1) κ⁻¹).transpose.mulVec v (shiftForward r)=
    κ^charge (r 0)*(physicalTransfer (N+1) κ).mulVec v (shiftForward r)
  rw [hc r]
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_assoc,← physicalTransfer_transpose_rotation N κ hκ]

end PolynomialVacuumAlgebra

end OAI
