import OAI.Combinatorics.PolynomialVacuum.Algebra.TraceTrain

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

def padCup (N : ℕ) (s : ℕ → Spin) : ℕ → Spin := insertOne N .zero (insertOne N .zero s)
@[simp] theorem padCup_left (N : ℕ) (s : ℕ → Spin) : padCup N s N=.zero := by simp [padCup]
@[simp] theorem padCup_right (N : ℕ) (s : ℕ → Spin) : padCup N s (N+1)=.zero := by simp [padCup]
@[simp] theorem padCup_skip (N : ℕ) (s : ℕ → Spin) : skipTwo N (padCup N s)=s := by
  funext j
  simp only [skipTwo,padCup,insertOne]
  split_ifs <;> first | rfl | (congr 1; omega)

theorem rotate_padCup_head (N : ℕ) (s : ℕ → Spin) (ab : Pair) :
    natRotate (N+1) (replacePair (padCup N s) N (N+1) ab) 0=ab.2 := by
  simp [natRotate,rotationIndex,replacePair]

theorem rotate_padCup_tail (N : ℕ) (s : ℕ → Spin) (ab : Pair) :
    ∀ j, j<N+1 → skipOne 0 (natRotate (N+1) (replacePair (padCup N s) N (N+1) ab)) j=
       insertOne N ab.1 s j := by
  intro j hj
  simp only [skipOne,not_lt_zero,ite_false,natRotate,Function.comp_apply,rotationIndex,
    Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,Nat.add_sub_cancel,
    replacePair,Function.update_apply,padCup,insertOne]
  split_ifs <;> first | rfl | (congr 1; omega)

theorem numerator_cup_zero (a : ℂ) (ab : Pair) :
    exchangeNumerator (T*a) a (.zero,.zero) ab=exchangeDenominator (T*a) a * cup ab := by
  rcases ab with ⟨b,c⟩
  cases b <;> cases c <;>
    norm_num [exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
      q_five_inv,T,t] <;> vacuum_ring_finish

theorem cup_trace_identity (f : Spin → Spin → ℂ) :
    (∑ ab : Pair,cup ab*zeta^(-charge ab.2)*(∑ h : Spin,cup (ab.2,h)*f h ab.1))=
      ∑ h : Spin,zeta^charge h*f h h := by
  simp only [Fintype.sum_prod_type,sum_spin,cup,charge]
  norm_num [zpow_neg,q_five_inv,zeta,T,t]
  vacuum_ring_finish

 

theorem cupRow_trace (N : ℕ) (a : ℂ) (W : SpinTensor ℕ ℂ) (hW : DependsBefore N W) (s : ℕ → Spin) :
    cupRowCircuit N a W (padCup N s)=
      exchangeDenominator (T*a) a * tracedTrain N (T*a) (fun _ => 1) W s := by
  have hX : skipOne 0 (frontFirstData a)=fun _ => (1 : ℂ) := by
    funext j; simp [skipOne,frontFirstData]
  have hv (ab : Pair) :
      braidTrain (T*a) (frontFirstData a) 1 N (cupLinear 0 W)
        (natRotate (N+1) (replacePair (padCup N s) N (N+1) ab))=
      ∑ h : Spin,cup (ab.2,h)*
        braidTrain (T*a) (fun _ => 1) 0 N (auxiliaryInput h W) (insertOne N ab.1 s) := by
    rw [braidTrain_head_evaluate,rotate_padCup_head,hX,cup_headFiber,map_sum]
    simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    apply braidTrain_depends (auxiliaryInput_depends hW h) (by omega)
    exact rotate_padCup_tail N s ab
  simp only [cupRowCircuit,siteR,pairLinear,LinearMap.coe_mk,AddHom.coe_mk,pairAction,
    padCup_left,padCup_right,numerator_cup_zero,rotateTensor,
    replacePair_right,hv,tracedTrain,mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [mul_assoc] using cup_trace_identity (fun h b =>
    braidTrain (T*a) (fun _ => 1) 0 N (auxiliaryInput h W) (insertOne N b s))

end PolynomialVacuumAlgebra

end OAI
