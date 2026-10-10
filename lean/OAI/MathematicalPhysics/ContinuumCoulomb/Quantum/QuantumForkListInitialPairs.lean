import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialSum

namespace OAI

/-! The even and odd entries in the initial endpoint table are precisely
the two couplings belonging to each physical singlet. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

def initialIndexEquiv (m : ℕ) : Fin m × Fin 2 ≃ Fin (2*m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))

theorem initialIndexEquiv_val (m : ℕ) (e : Fin m) (b : Fin 2) :
    (initialIndexEquiv m (e,b)).val=2*e.val+b.val := by
  change b.val+2*e.val=2*e.val+b.val
  omega

theorem initial_evenodd_sum {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → M) :
    ((List.range (2*m)).map f).sum=∑ e : Fin m, (f (2*e.val)+f (2*e.val+1)) := by
  rw [range_sum]
  have h := (initialIndexEquiv m).sum_comp (fun j => f j.val)
  simpa only [Fintype.sum_prod_type,Fin.sum_univ_two,initialIndexEquiv_val,
    Fin.val_zero,Fin.val_one,add_zero] using h.symm

theorem initialBond_pair (bs : List Bond) (e : Fin bs.length) (b : Fin 2) :
    initialBond bs (2*e.val+b.val)=bs[e.val] := by
  have hd : (2*e.val+b.val)/2=e.val := by have := b.isLt; omega
  simp only [initialBond,hd,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem e.isLt,Option.getD_some]

theorem initialEndpoint_even (bs : List Bond) (e : Fin bs.length) :
    initialEndpoint bs (2*e.val)=bs[e.val].1 := by
  have hm : (2*e.val)%2=0 := by omega
  simp only [initialEndpoint,hm,ite_true]
  simpa only [Fin.val_zero,add_zero] using
    congrArg Prod.fst (initialBond_pair bs e 0)

theorem initialEndpoint_odd (bs : List Bond) (e : Fin bs.length) :
    initialEndpoint bs (2*e.val+1)=bs[e.val].2.1 := by
  have hm : (2*e.val+1)%2≠0 := by omega
  simp only [initialEndpoint,hm,ite_false]
  exact congrArg (fun p : Bond => p.2.1) (initialBond_pair bs e 1)

theorem initialWeight_even (bs : List Bond) (R : ℚ) (e : Fin bs.length) :
    initialWeight bs R (2*e.val)=R := by
  have hm : (2*e.val)%2=0 := by omega
  simp only [initialWeight,hm,ite_true]

theorem initialWeight_odd (bs : List Bond) (R : ℚ) (e : Fin bs.length) :
    initialWeight bs R (2*e.val+1)=2*R*bs[e.val].2.2 := by
  have hm : (2*e.val+1)%2≠0 := by omega
  simp only [initialWeight,hm,ite_false]
  simpa only [Fin.val_one] using
    congrArg (fun b : Bond => 2*R*b.2.2) (initialBond_pair bs e 1)

theorem initial_group_pair_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (R : ℚ) (f : ℕ → Port → M) :
    ((List.range n).map (fun i => ((initialGroup n bs R i).map (f i)).sum)).sum =
      ∑ e : Fin bs.length,
        (f bs[e.val].1 (n+2*e.val,R)+
          f bs[e.val].2.1 (n+(2*e.val+1),2*R*bs[e.val].2.2)) := by
  rw [initial_group_sum n bs hb,initial_evenodd_sum]
  simp only [initialEndpoint_even,initialEndpoint_odd,initialWeight_even,initialWeight_odd]

end ContinuumCoulomb.QuantumForkList

end

end OAI
