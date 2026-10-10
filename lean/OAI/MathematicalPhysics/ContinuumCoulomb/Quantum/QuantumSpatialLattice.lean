import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialPlanarRealization
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticeSourceBounds

namespace OAI

/-! The specified nearest-neighbor output of a degree-three spatial model.
The graph, positions, source thresholds and estimates refer to one construction. -/

noncomputable section
namespace ContinuumCoulomb.QMASpatialExchangeModel
open scoped Classical
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)
variable (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)

def latticeGraph (N : ℚ) :=
  (M.portRouteData hA hd).latticeGraph N (M.bufferedPath_length hd)
    (M.sourceCell_no_passage hA hd) M.placedVertex_positive

def latticePosition (N : ℚ) :=
  (M.portRouteData hA hd).latticePosition N (M.bufferedPath_length hd)
    (M.sourceCell_no_passage hA hd) M.placedVertex_positive

theorem lattice_vertices_ge (N : ℚ) : M.n ≤ (M.latticeGraph hA hd N).n :=
  (M.portRouteData hA hd).lattice_vertices_ge N (M.bufferedPath_length hd)
    (M.sourceCell_no_passage hA hd) M.placedVertex_positive

theorem lattice_position_injective (N : ℚ) :
    Function.Injective (M.latticePosition hA hd N) :=
  (M.portRouteData hA hd).lattice_position_injective N (M.bufferedPath_length hd)
    (M.sourceCell_no_passage hA hd) M.placedVertex_positive

theorem lattice_adjacent (N : ℚ) (e : (M.latticeGraph hA hd N).Edge) :
    qmaSquareGrid.Adj
      (M.latticePosition hA hd N ((M.latticeGraph hA hd N).left e))
      (M.latticePosition hA hd N ((M.latticeGraph hA hd N).right e)) :=
  (M.portRouteData hA hd).lattice_adjacent N (M.bufferedPath_length hd)
    (M.sourceCell_no_passage hA hd) M.placedVertex_positive e

theorem lattice_bounded (N : ℚ) (v : Fin (M.latticeGraph hA hd N).n) :
    (M.latticePosition hA hd N v).1 < 256*M.bufferedWidth ∧
      (M.latticePosition hA hd N v).2 < 256*M.bufferedHeight := by
  apply (M.portRouteData hA hd).lattice_bounded N (M.bufferedPath_length hd)
    (M.sourceCell_no_passage hA hd) M.placedVertex_positive M.placedVertex_bounds
  intro e k _
  exact M.bufferedPath_bounds hd e ((M.bufferedPath hd e).val.getVert_mem_support k)

theorem lattice_energy_error {N : ℚ} (hN : 0 < N) :
    |(M.latticeGraph hA hd N).energy-M.energy| ≤
      ((routeLengthBound A B+82:ℕ):ℝ)/(N:ℝ) :=
  (M.portRouteData hA hd).lattice_energy_error N (M.bufferedPath_length hd)
    (M.sourceCell_no_passage hA hd) M.placedVertex_positive hN

theorem lattice_energy_error_nat (N : ℕ) (hN : 0 < N) :
    |(M.latticeGraph hA hd (N:ℚ)).energy-M.energy| ≤
      ((routeLengthBound A B:ℝ)+82)/(N:ℝ) := by
  have h := M.lattice_energy_error hA hd (N := (N:ℚ)) (by exact_mod_cast hN)
  simpa only [Nat.cast_add,Nat.cast_ofNat,Rat.cast_natCast] using h

def latticeSource (N : ℚ) (hn : 0 < M.n) (a b : ℚ) (hab : a < b) :
    SquareLatticeHeisenberg :=
  (M.portRouteData hA hd).latticeSource N (M.bufferedPath_length hd)
    (M.sourceCell_no_passage hA hd) M.placedVertex_positive hn a b hab

theorem latticeSource_energy (N : ℚ) (hn : 0 < M.n) (a b : ℚ) (hab : a < b) :
    realSourceGroundEnergy (M.latticeSource hA hd N hn a b hab) =
      (M.latticeGraph hA hd N).energy-((M.latticeGraph hA hd N).constant:ℝ) :=
  (M.portRouteData hA hd).latticeSource_energy N (M.bufferedPath_length hd)
    (M.sourceCell_no_passage hA hd) M.placedVertex_positive hn a b hab

theorem latticeSource_binary_promise (N : ℚ) (hn : 0 < M.n) (a b : ℚ) (hab : a < b)
    {n k L T : ℕ} (hsize : n ≤ M.n)
    (hN : 0 ≤ N) (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T)
    (hc : M.exchangeGraph.CoefficientBound L)
    (hx : (256*M.bufferedWidth:ℕ) ≤ (n+1:ℝ)^k)
    (hy : (256*M.bufferedHeight:ℕ) ≤ (n+1:ℝ)^k)
    (hw : (QuantumCoefficientPrograms.latticeBound (routeLengthBound A B)
      (Fintype.card M.Term) (M.portRouteData hA hd).crossingCells.card L T:ℝ) ≤ (n+1:ℝ)^k)
    (hg : ((n+1:ℝ)^k)⁻¹ ≤ (b:ℝ)-a) :
    (M.latticeSource hA hd N hn a b hab).binary.PolynomialPromise k := by
  apply (M.portRouteData hA hd).latticeSource_binary_promise N
    (M.bufferedPath_length hd) (M.sourceCell_no_passage hA hd) M.placedVertex_positive
    hn a b hab hsize M.placedVertex_bounds ?_ hN hL hT hc hx hy hw hg
  intro e j _
  exact M.bufferedPath_bounds hd e ((M.bufferedPath hd e).val.getVert_mem_support j)

end ContinuumCoulomb.QMASpatialExchangeModel

end

end OAI
