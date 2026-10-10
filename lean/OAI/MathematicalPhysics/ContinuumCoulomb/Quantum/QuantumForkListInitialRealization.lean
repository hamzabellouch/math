import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialPhysical

namespace OAI

/-! Reordering the actual initial bond list gives exactly the typed physical
singlet Hamiltonian, including its scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample MediatorListProgram
open scoped BigOperators Classical

def initialSourceBonds (n : ℕ) (bs : List Bond) (R : ℚ) : List Bond :=
  (List.range bs.length).map (fun e => (n+2*e,n+2*e+1,R^2))++
    activeBonds ((List.range n).map (initialGroup n bs R))

theorem initialPhysical_sum {M : Type*} [AddCommMonoid M] {n m : ℕ}
    (left right : Fin m → Fin n) (J : Fin m → ℚ) (R : ℚ) (f : Bond → M) :
    ((initialPhysicalBonds left right J R).map f).sum =
      (∑ e : Fin m, f (n+2*e.val,n+2*e.val+1,R^2))+
      ∑ e : Fin m,
        (f ((left e).val,n+2*e.val,R)+f ((right e).val,n+2*e.val+1,2*R*J e)) := by
  simp only [initialPhysicalBonds,List.map_append,List.sum_append,List.map_ofFn,
    List.sum_ofFn,List.map_flatten,List.sum_flatten,Function.comp_def,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,add_zero,erase,MediatorIteration.old_val,
    MediatorIteration.fresh_val,Fin.val_zero,Fin.val_one]

theorem initialSource_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (R : ℚ) (f : Bond → M) :
    ((initialSourceBonds n bs R).map f).sum =
      ((initialPhysicalBonds (SourceBondLists.bonds n bs hb).left
        (SourceBondLists.bonds n bs hb).right (fun e => (bs.get e).2.2) R).map f).sum := by
  simp only [initialSourceBonds,List.map_append,List.sum_append,List.map_map,
    Function.comp_def,range_sum,initial_active_sum n bs hb,initialPhysical_sum,
    SourceBondLists.bonds,List.get_eq_getElem]
  congr 1

theorem initial_constant_eq (n : ℕ) (bs : List Bond) (c N : ℚ) :
    (initial n bs c N).2.2.1 =
      initialConstant (fun e : Fin bs.length => (bs.get e).2.2) c (initialScale N bs c) := by
  have hh : (bs.map (fun b => (3/4+3*b.2.2^2:ℚ))).sum =
      ∑ e : Fin bs.length, (3/4+3*(bs.get e).2.2^2) := by
    rw [← List.sum_ofFn]
    exact congrArg List.sum (List.ofFn_getElem_eq_map bs
      (fun b => (3/4+3*b.2.2^2:ℚ))).symm
  change c+(bs.map (fun b => (3/4+3*b.2.2^2:ℚ))).sum+
    3*(bs.length:ℚ)*(initialScale N bs c)^2 = _
  rw [hh]
  rfl

theorem initial_bottom_physical (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (c N : ℚ) :
    normalizedBottom (matrix (initial n bs c N)) =
      rawBottom (n+bs.length*2)
        (initialPhysicalBonds (SourceBondLists.bonds n bs hb).left
          (SourceBondLists.bonds n bs hb).right (fun e => (bs.get e).2.2) (initialScale N bs c),
        initialConstant (fun e : Fin bs.length => (bs.get e).2.2) c (initialScale N bs c)) := by
  have hh : rawMatrix (n+2*bs.length)
      (initialSourceBonds n bs (initialScale N bs c),(initial n bs c N).2.2.1) =
      rawMatrix (n+2*bs.length)
        (initialPhysicalBonds (SourceBondLists.bonds n bs hb).left
          (SourceBondLists.bonds n bs hb).right (fun e => (bs.get e).2.2) (initialScale N bs c),
        initialConstant (fun e : Fin bs.length => (bs.get e).2.2) c (initialScale N bs c)) := by
    unfold rawMatrix
    rw [initialSource_sum n bs hb,initial_constant_eq]
  change rawBottom (n+2*bs.length)
    (initialSourceBonds n bs (initialScale N bs c),(initial n bs c N).2.2.1)=_
  calc
    _ = rawBottom (n+2*bs.length)
        (initialPhysicalBonds (SourceBondLists.bonds n bs hb).left
          (SourceBondLists.bonds n bs hb).right (fun e => (bs.get e).2.2) (initialScale N bs c),
        initialConstant (fun e : Fin bs.length => (bs.get e).2.2) c (initialScale N bs c)) :=
      congrArg normalizedBottom hh
    _ = _ := by rw [Nat.mul_comm 2 bs.length]

end ContinuumCoulomb.QuantumForkList

end

end OAI
