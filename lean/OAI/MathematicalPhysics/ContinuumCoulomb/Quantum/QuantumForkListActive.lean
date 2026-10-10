import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListPartition
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListMatrix

namespace OAI

/-! Exact active-star matrices of the ordered compiler state. The pairing
identity applies to every matrix entry, including the retained odd port. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange

def starBonds (i : ℕ) (ps : List Port) : List Bond :=
  ps.map (fun p => (i,p.1,p.2))

def activeBonds (gs : Groups) : List Bond :=
  ((List.range gs.length).map (fun i => starBonds i (groupAt gs i))).flatten

def unpairedBonds (gs : Groups) : List Bond :=
  ((List.range gs.length).map (fun i => starBonds i (unpaired (groupAt gs i)))).flatten

def pairedBonds (gs : Groups) : List Bond :=
  (catalog gs).flatMap (fun p => [(p.1,p.2.1.1,p.2.1.2),(p.1,p.2.2.1,p.2.2.2)])

theorem catalog_sum {M : Type*} [AddCommMonoid M] (gs : Groups) (f : TaggedPair → M) :
    ((catalog gs).map f).sum =
      ((List.range gs.length).map (fun i =>
        ((pairs (groupAt gs i)).map (fun p => f (i,p))).sum)).sum := by
  simp only [catalog,List.map_flatten,List.sum_flatten,List.map_map,Function.comp_def]

theorem active_pairing {M : Type*} [AddCommMonoid M] (gs : Groups) (f : Bond → M) :
    ((activeBonds gs).map f).sum =
      ((pairedBonds gs).map f).sum+((unpairedBonds gs).map f).sum := by
  have hp : ((List.range gs.length).map (fun i =>
      ((groupAt gs i).map (fun p => f (i,p.1,p.2))).sum)) =
      (List.range gs.length).map (fun i =>
        ((pairs (groupAt gs i)).map (fun p => f (i,p.1.1,p.1.2)+f (i,p.2.1,p.2.2))).sum+
        ((unpaired (groupAt gs i)).map (fun p => f (i,p.1,p.2))).sum) := by
    apply List.map_congr_left
    intro i _
    exact paired_sum (fun p => f (i,p.1,p.2)) (groupAt gs i)
  simp only [activeBonds,starBonds,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def]
  rw [hp,List.sum_map_add]
  congr 1
  · symm
    simp only [pairedBonds,List.flatMap_def,List.map_flatten,List.sum_flatten,
      List.map_map,Function.comp_def,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,add_zero]
    exact catalog_sum gs (fun p => f (p.1,p.2.1.1,p.2.1.2)+f (p.1,p.2.2.1,p.2.2.2))
  · simp only [unpairedBonds,starBonds,List.map_flatten,List.sum_flatten,List.map_map,
      Function.comp_def]

def matrix (s : State) := rawMatrix s.1 (s.2.1++activeBonds s.2.2.2,s.2.2.1)

theorem matrix_pairing (s : State) : matrix s =
    rawMatrix s.1 (s.2.1++unpairedBonds s.2.2.2,s.2.2.1)+
      ((pairedBonds s.2.2.2).map (rawBondMatrix s.1)).sum := by
  simp only [matrix,rawMatrix,List.map_append,List.sum_append,
    active_pairing s.2.2.2 (rawBondMatrix s.1)]
  abel

end ContinuumCoulomb.QuantumForkList

end

end OAI
