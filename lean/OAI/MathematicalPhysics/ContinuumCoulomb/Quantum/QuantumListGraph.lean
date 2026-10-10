import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalPathStep
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceBondLists

namespace OAI

/-! Exact exchange-graph semantics for the finite bond lists manipulated by
the routing compiler. The scalar offset stays part of the full Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListGraph
open Matrix MediatorListProgram
open scoped BigOperators Classical

def ofBonds (n : ℕ) (xs : List Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n xs) (hn : ∀ e ∈ xs, e.1 ≠ e.2.1) :
    QMARationalExchangeGraph where
  n := n
  Edge := Fin xs.length
  left := (SourceBondLists.bonds n xs hb).left
  right := (SourceBondLists.bonds n xs hb).right
  distinct := fun i h => hn _ (List.get_mem xs i) (congrArg Fin.val h)
  weight := (SourceBondLists.bonds n xs hb).weight
  constant := c

theorem ofBonds_matrix (n : ℕ) (xs : List Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n xs) (hn : ∀ e ∈ xs, e.1 ≠ e.2.1) :
    qmaExchangeMatrix (n := n) (ofBonds n xs c hb hn).left (ofBonds n xs c hb hn).right
      (fun e => ((ofBonds n xs c hb hn).weight e:ℝ)) c =
      SourceBondLists.matrix n xs+(c:ℂ) • 1 := by
  rw [SourceBondLists.matrix_bonds n xs hb]
  simp only [ofBonds,qmaExchangeMatrix,MediatorIteration.Bonds.matrix,sourceGraphMatrix,
    Complex.ofReal_ratCast]
  rfl

theorem ofBonds_energy (n : ℕ) (xs : List Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n xs) (hn : ∀ e ∈ xs, e.1 ≠ e.2.1) :
    (ofBonds n xs c hb hn).energy =
      sourceMatrixBottom n (SourceBondLists.matrix n xs+(c:ℂ) • 1) := by
  exact congrArg (sourceMatrixBottom n) (ofBonds_matrix n xs c hb hn)

def packed (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m) : List Bond :=
  List.ofFn fun i => ((G.left (labels.symm i)).val,(G.right (labels.symm i)).val,
    G.weight (labels.symm i))

theorem packed_bounded (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m) :
    SourceBondLists.bounded G.n (packed G labels) := by
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact ⟨(G.left (labels.symm i)).isLt,(G.right (labels.symm i)).isLt⟩

theorem packed_noLoops (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m) :
    ∀ e ∈ packed G labels, e.1 ≠ e.2.1 := by
  intro e he h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact G.distinct (labels.symm i) (Fin.ext h)

theorem packed_matrix (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m) :
    SourceBondLists.matrix G.n (packed G labels)+(G.constant:ℂ) • 1 =
      qmaExchangeMatrix G.left G.right (fun e => (G.weight e:ℝ)) G.constant := by
  have he (i : Fin m) :
      SourceBondLists.bondMatrix G.n
        ((G.left (labels.symm i)).val,(G.right (labels.symm i)).val,G.weight (labels.symm i)) =
      (G.weight (labels.symm i):ℂ) •
        sourceHeisenbergMatrix G.n (G.left (labels.symm i)) (G.right (labels.symm i)) := by
    rw [SourceBondLists.bondMatrix,dite_eq_left
      ⟨(G.left (labels.symm i)).isLt,(G.right (labels.symm i)).isLt⟩]
  simp only [SourceBondLists.matrix,packed,List.map_ofFn,List.sum_ofFn,Function.comp_apply,he,
    qmaExchangeMatrix,Complex.ofReal_ratCast]
  exact congrArg (fun x => x+(G.constant:ℂ) • 1)
    (labels.symm.sum_comp (fun e => (G.weight e:ℂ) •
      sourceHeisenbergMatrix G.n (G.left e) (G.right e)))

theorem packed_energy (G : QMARationalExchangeGraph) {m : ℕ} (labels : G.Edge ≃ Fin m) :
    (ofBonds G.n (packed G labels) G.constant (packed_bounded G labels)
      (packed_noLoops G labels)).energy = G.energy := by
  exact (ofBonds_energy _ _ _ _ _).trans
    (congrArg (sourceMatrixBottom G.n) (packed_matrix G labels))

end ContinuumCoulomb.QuantumListGraph

end

end OAI
