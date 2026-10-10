import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMergeEdges
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridWalk
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceMatrix

namespace OAI

/-! Convert an actual simple rational grid graph into the field-free source
Hamiltonian, retaining the exact scalar shift in its thresholds. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaGridCoordinate (p : ℕ × ℕ) : ℤ × ℤ := (p.1,p.2)

theorem qmaGridCoordinate_injective : Function.Injective qmaGridCoordinate := by
  intro p q h
  apply Prod.ext
  · exact_mod_cast (show (p.1:ℤ) = q.1 from congrArg Prod.fst h)
  · exact_mod_cast (show (p.2:ℤ) = q.2 from congrArg Prod.snd h)

theorem qmaNatDistance (a b : ℕ) : Int.natAbs ((a:ℤ)-b) = Nat.dist a b := by
  rcases le_total a b with h | h
  · rw [Int.natAbs_natCast_sub_natCast_of_le h,Nat.dist_eq_sub_of_le h]
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h,Nat.dist_eq_sub_of_le_right h]

theorem qmaGridCoordinate_adj {p q : ℕ × ℕ} (h : qmaSquareGrid.Adj p q) :
    Int.natAbs ((qmaGridCoordinate p).1-(qmaGridCoordinate q).1)+
      Int.natAbs ((qmaGridCoordinate p).2-(qmaGridCoordinate q).2) = 1 := by
  simpa only [qmaGridCoordinate,qmaNatDistance] using (show Nat.dist p.1 q.1 + Nat.dist p.2 q.2 = 1 from h)

namespace QMARationalExchangeGraph
variable (G : QMARationalExchangeGraph)

def Simple : Prop := ∀ e f : G.Edge, e ≠ f →
  ¬(G.left e = G.left f ∧ G.right e = G.right f) ∧
  ¬(G.left e = G.right f ∧ G.right e = G.left f)

theorem merge_simple : G.merge.Simple := by
  intro e f hef
  constructor
  · rintro ⟨hl,hr⟩
    exact hef (G.merge_pair_injective (Prod.ext hl hr))
  · rintro ⟨hl,hr⟩
    have he : G.merge.left e < G.merge.right e := G.mergedEdge_lt e
    have hf : G.merge.left f < G.merge.right f := G.mergedEdge_lt f
    rw [hl,hr] at he
    exact (not_lt_of_ge hf.le) he

def latticeSource (hn : 0 < G.n) (position : Fin G.n → ℕ × ℕ)
    (hinj : Function.Injective position)
    (hgrid : ∀ e, qmaSquareGrid.Adj (position (G.left e)) (position (G.right e)))
    (hsimple : G.Simple) (a b : ℚ) (hab : a < b) : SquareLatticeHeisenberg where
  vertices := G.n
  vertices_pos := hn
  coordinate := qmaGridCoordinate ∘ position
  coordinate_injective := qmaGridCoordinate_injective.comp hinj
  edges := Fintype.card G.Edge
  left e := G.left ((Fintype.equivFin G.Edge).symm e)
  right e := G.right ((Fintype.equivFin G.Edge).symm e)
  adjacent _e := qmaGridCoordinate_adj (hgrid _)
  edge_simple _e _f hef := hsimple _ _ (fun h => hef ((Fintype.equivFin G.Edge).symm.injective h))
  coefficient e := G.weight ((Fintype.equivFin G.Edge).symm e)
  lower := a-G.constant
  upper := b-G.constant
  gap_pos := sub_lt_sub_right hab _

theorem latticeSource_matrix (hn : 0 < G.n) (position : Fin G.n → ℕ × ℕ)
    (hinj : Function.Injective position)
    (hgrid : ∀ e, qmaSquareGrid.Adj (position (G.left e)) (position (G.right e)))
    (hsimple : G.Simple) (a b : ℚ) (hab : a < b) :
    (G.latticeSource hn position hinj hgrid hsimple a b hab).bonds.matrix =
      qmaExchangeMatrix G.left G.right (fun e => (G.weight e:ℝ)) G.constant -
        (G.constant:ℂ) • (1 : Matrix (SourceSpinBasis G.n) (SourceSpinBasis G.n) ℂ) := by
  have hs := (Fintype.equivFin G.Edge).symm.sum_comp (fun e =>
    (G.weight e:ℂ) • sourceHeisenbergMatrix G.n (G.left e) (G.right e))
  change (∑ e : Fin (Fintype.card G.Edge),
    (G.weight ((Fintype.equivFin G.Edge).symm e):ℂ) •
      sourceHeisenbergMatrix G.n (G.left ((Fintype.equivFin G.Edge).symm e))
        (G.right ((Fintype.equivFin G.Edge).symm e))) = _
  rw [hs]
  simp only [qmaExchangeMatrix,Complex.ofReal_ratCast,add_sub_cancel_right]

theorem latticeSource_energy (hn : 0 < G.n) (position : Fin G.n → ℕ × ℕ)
    (hinj : Function.Injective position)
    (hgrid : ∀ e, qmaSquareGrid.Adj (position (G.left e)) (position (G.right e)))
    (hsimple : G.Simple) (a b : ℚ) (hab : a < b) :
    realSourceGroundEnergy (G.latticeSource hn position hinj hgrid hsimple a b hab) =
      G.energy-(G.constant:ℝ) := by
  rw [← sourceMatrixBottom_eq_realSource,G.latticeSource_matrix]
  change sourceMatrixBottom G.n
    (qmaExchangeMatrix G.left G.right (fun e => (G.weight e:ℝ)) G.constant -
      (G.constant:ℂ) • 1) = G.energy-(G.constant:ℝ)
  simpa only [energy,Complex.ofReal_ratCast] using
    sourceMatrixBottom_shift G.n
      (qmaExchangeMatrix G.left G.right (fun e => (G.weight e:ℝ)) G.constant) (G.constant:ℝ)

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
