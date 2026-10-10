import OAI.Combinatorics.PolynomialVacuum.Pairing.RowPeriodic

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder

def oppositeSpin : Spin → Spin
  | .zero => .zero | .plus => .minus | .minus => .plus
@[simp] theorem oppositeSpin_invol (h : Spin) : oppositeSpin (oppositeSpin h)=h := by cases h <;> rfl
@[simp] theorem charge_oppositeSpin (h : Spin) : charge (oppositeSpin h)= -charge h := by cases h <;> rfl
def oppositeSpinEquiv : Spin ≃ Spin := ⟨oppositeSpin,oppositeSpin,oppositeSpin_invol,oppositeSpin_invol⟩
noncomputable def triangleUp (h j a : Spin) : ℂ := arrowVertexWeight (-charge j) (-charge h) (charge a)
noncomputable def triangleDown (h j a : Spin) : ℂ := arrowVertexWeight (charge j) (charge h) (-charge a)

theorem triangleUp_dual (h j a : Spin) : triangleUp h j a=triangleDown (oppositeSpin a) j (oppositeSpin h) := by
  simp only [triangleUp,triangleDown,arrowVertexWeight,up_ice,down_ice]
  cases h <;> cases j <;> cases a <;>
    norm_num [charge,oppositeSpin,vertexOccupation,cubicTurn]
theorem triangleDown_dual (h j a : Spin) : triangleDown h j a=triangleUp (oppositeSpin a) j (oppositeSpin h) := by
  rw [triangleUp_dual]; simp

noncomputable def triangleRowWeight {N : ℕ} (out inp a k : Fin (N+1) → Spin) : ℂ :=
  ∏j,triangleUp (k j) (inp j) (a j)*triangleDown (k j) (out j) (a (j-1))

theorem finite_angle_product {α : Type*} [Fintype α] (f : α → ℤ) :
    ∏i,anglePhase (f i)=anglePhase (∑i,f i) := by
  classical
  have hh : ∀s : Finset α,∏i∈s,anglePhase (f i)=anglePhase (∑i∈s,f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha,ih]
  exact hh Finset.univ

theorem row_triangle_weight {N : ℕ} (out inp a k : Fin (N+1) → Spin) :
    (∏j,honeycombPiece (out j,a j) (a (j-1),inp j) (k j))=triangleRowWeight out inp a k := by
  simp_rw [honeycombPiece_arrows]
  rw [Finset.prod_mul_distrib,finite_angle_product]
  have hs : (∑j : Fin (N+1),charge (a (j-1)))=∑j,charge (a j) := by
    simpa only [sub_eq_add_neg,Equiv.coe_addRight] using Equiv.sum_comp (Equiv.addRight (-1 : Fin (N+1))) (fun j=>charge (a j))
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,hs,sub_self,mul_zero,anglePhase_zero,mul_one]
  rfl

def shiftForward {N : ℕ} (s : Fin (N+1) → Spin) : Fin (N+1) → Spin := fun j=>s (j+1)
def dualAux {N : ℕ} (k : Fin (N+1) → Spin) : Fin (N+1) → Spin := fun j=>oppositeSpin (k (j+1))
def dualInternal {N : ℕ} (a : Fin (N+1) → Spin) : Fin (N+1) → Spin := fun j=>oppositeSpin (a j)

theorem triangleRowWeight_dual {N : ℕ} (out inp a k : Fin (N+1) → Spin) :
    triangleRowWeight out inp a k=triangleRowWeight inp (shiftForward out) (dualAux k) (dualInternal a) := by
  unfold triangleRowWeight
  simp only [shiftForward,dualAux,dualInternal,sub_add_cancel,← triangleDown_dual,← triangleUp_dual]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,mul_comm]
  congr 1
  symm
  simpa only [Equiv.coe_addRight,add_sub_cancel_right] using Equiv.prod_comp (Equiv.addRight (1 : Fin (N+1))) (fun j=>triangleDown (k j) (out j) (a (j-1)))

theorem triangleRowWeight_zero_ice {N : ℕ} (out inp a k : Fin (N+1) → Spin)
    (hw : triangleRowWeight out inp a k≠0) :
    charge (a (Fin.last N))=charge (k 0)+charge (out 0) := by
  have hh := (Finset.prod_ne_zero_iff.mp hw) 0 (Finset.mem_univ _)
  have hd := (mul_ne_zero_iff.mp hh).2
  have hprev : (0-1 : Fin (N+1))=Fin.last N := by apply Fin.ext; simp
  rw [hprev] at hd
  unfold triangleDown arrowVertexWeight at hd
  split_ifs at hd with hc
  · exact (down_ice _ _ _).mp hc
  · exact (hd rfl).elim

end PolynomialVacuumAlgebra

end OAI
