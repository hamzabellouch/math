import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialMatrix

namespace OAI

/-! The initial emitted couplings are the simultaneous odd-path singlet
Hamiltonian used by the already proved full-space perturbation estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample
open scoped BigOperators Classical

def initialPhysicalBonds {n m : ℕ} (left right : Fin m → Fin n) (J : Fin m → ℚ)
    (R : ℚ) : List MediatorListProgram.Bond :=
  (List.ofFn (fun e => erase (fresh n m e 0,fresh n m e 1,R^2)))++
    (List.ofFn (fun e => [erase (old n m (left e),fresh n m e 0,R),
      erase (old n m (right e),fresh n m e 1,2*R*J e)])).flatten

def initialConstant {m : ℕ} (J : Fin m → ℚ) (c R : ℚ) : ℚ :=
  (c+∑ e, (3/4+3*(J e)^2))+3*m*R^2

theorem initialPhysical_matrix {n m : ℕ} (left right : Fin m → Fin n)
    (J : Fin m → ℚ) (c R : ℚ) :
    rawMatrix (n+m*2) (initialPhysicalBonds left right J R,initialConstant J c R) =
      qmaPathsGraph (fun a : Fin 0 => Fin.elim0 a) (fun a : Fin 0 => Fin.elim0 a)
        (fun _ => 0) (c:ℝ) (R:ℝ) (qmaOriginalSite left right) (fun _ => false)
          (fun e => (J e:ℝ)) := by
  simp only [rawMatrix,← Rat.cast_smul_eq_qsmul ℂ,initialPhysicalBonds,List.map_append,
    List.sum_append,List.map_ofFn,List.sum_ofFn,List.map_flatten,List.sum_flatten,
    Function.comp_def,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    rawBondMatrix_erase,typedBondMatrix]
  simp only [qmaPathsGraph,qmaExchangeMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_two,qmaParallelGraphLeft,qmaParallelGraphRight,qmaParallelGraphWeight,
    qmaPathAmplitude,qmaPathMember,qmaOriginalSite,qmaPathOffset,
    Finset.univ_eq_empty,Finset.sum_empty,zero_add,
    initialConstant]
  push_cast
  simp only [Finset.sum_add_distrib]

end ContinuumCoulomb.QuantumForkList

end

end OAI
