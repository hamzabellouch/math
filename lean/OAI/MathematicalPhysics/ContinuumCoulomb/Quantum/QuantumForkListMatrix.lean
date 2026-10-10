import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListData
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorListCorrectness

namespace OAI

/-! The four literal bonds emitted for one port pair are exactly its
correction, singlet penalty and two outer couplings in the fork Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample

def typedPairBonds (n r : ℕ) (e : Fin r) (a b : Fin n) (J K R : ℚ) :
    List (TypedBond (n+r*2)) :=
  [(old n r a,old n r b,2*J*K),
   (fresh n r e 0,fresh n r e 1,R^2),
   (old n r a,fresh n r e 1,2*R*J),
   (old n r b,fresh n r e 1,2*R*K)]

theorem pairBonds_eq (n r : ℕ) (e : Fin r) (a b : Fin n) (J K R : ℚ) :
    pairBonds n e.val R ((a.val,J),(b.val,K))=
      (typedPairBonds n r e a b J K R).map erase := by
  simp [pairBonds,typedPairBonds,erase,MediatorIteration.old_val,
    MediatorIteration.fresh_val]

theorem pairBonds_matrix (n r : ℕ) (e : Fin r) (a b : Fin n) (J K R : ℚ) :
    ((pairBonds n e.val R ((a.val,J),(b.val,K))).map (rawBondMatrix (n+r*2))).sum =
      ((2*J*K:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r a) (old n r b) +
      (((R^2:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (fresh n r e 0) (fresh n r e 1) +
      (((2*R*J:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r a) (fresh n r e 1) +
      ((2*R*K:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r b) (fresh n r e 1))) := by
  rw [pairBonds_eq,List.map_map]
  simp only [Function.comp_def,rawBondMatrix_erase,typedPairBonds,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,typedBondMatrix,add_zero]

end ContinuumCoulomb.QuantumForkList

end

end OAI
