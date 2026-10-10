import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticePromise
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticeCoefficient

namespace OAI

/-! The proved physical box and coefficient estimates imply the exact binary
source promise, measured against the retained input size. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMARationalExchangeGraph
variable (G : QMARationalExchangeGraph)

theorem latticeSource_binary_promise (hn : 0 < G.n) (position : Fin G.n → ℕ × ℕ)
    (hinj : Function.Injective position)
    (hgrid : ∀ e, qmaSquareGrid.Adj (position (G.left e)) (position (G.right e)))
    (hsimple : G.Simple) (a b : ℚ) (hab : a < b) {n k : ℕ} {C : ℝ}
    (hsize : n ≤ G.n)
    (hposition : ∀ v, (position v).1 ≤ (n+1:ℝ)^k ∧ (position v).2 ≤ (n+1:ℝ)^k)
    (hC : G.CoefficientBound C) (hCsize : C ≤ (n+1:ℝ)^k)
    (hg : ((n+1:ℝ)^k)⁻¹ ≤ (b:ℝ)-a) :
    (G.latticeSource hn position hinj hgrid hsimple a b hab).binary.PolynomialPromise k := by
  apply SquareLatticeHeisenberg.binary_polynomialPromise
    (G.latticeSource hn position hinj hgrid hsimple a b hab) n k hsize
  · intro i
    change |(((position i).1:ℤ):ℝ)| ≤ _ ∧ |(((position i).2:ℤ):ℝ)| ≤ _
    simp only [Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ) ≤ ((position i).1:ℝ)),
      abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ) ≤ ((position i).2:ℝ))]
    exact hposition i
  · intro e
    exact (hC.2 ((Fintype.equivFin G.Edge).symm e)).trans hCsize
  · change ((n+1:ℝ)^k)⁻¹ ≤ ((b-G.constant:ℚ):ℝ)-((a-G.constant:ℚ):ℝ)
    push_cast
    linarith

end QMARationalExchangeGraph

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
variable (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
variable (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
variable (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)

theorem latticeSource_binary_promise (hn : 0 < G.n) (a b : ℚ) (hab : a < b)
    {n k X Y L T : ℕ} (hsize : n ≤ G.n)
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e j, j ≤ P.length e → (P.point e j).1 < X ∧ (P.point e j).2 < Y)
    (hN : 0 ≤ N) (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : G.CoefficientBound L)
    (hx : (256*X:ℕ) ≤ (n+1:ℝ)^k) (hy : (256*Y:ℕ) ≤ (n+1:ℝ)^k)
    (hw : (QuantumCoefficientPrograms.latticeBound D (Fintype.card G.Edge)
      P.crossingCells.card L T : ℝ) ≤ (n+1:ℝ)^k)
    (hg : ((n+1:ℝ)^k)⁻¹ ≤ (b:ℝ)-a) :
    (P.latticeSource N hD havoid hpositive hn a b hab).binary.PolynomialPromise k := by
  apply (P.latticeGraph N hD havoid hpositive).latticeSource_binary_promise
    (hn.trans_le (P.lattice_vertices_ge N hD havoid hpositive))
    (P.latticePosition N hD havoid hpositive)
    (P.lattice_position_injective N hD havoid hpositive)
    (P.lattice_adjacent N hD havoid hpositive)
    (QMARationalExchangeGraph.merge_simple _) a b hab
    (hsize.trans (P.lattice_vertices_ge N hD havoid hpositive)) ?_
    (P.lattice_coefficientBound hN hD havoid hpositive hL hT hc) hw hg
  intro i
  have hb := P.lattice_bounded N hD havoid hpositive hsource hpath i
  exact ⟨(le_of_lt (by exact_mod_cast hb.1)).trans hx,
    (le_of_lt (by exact_mod_cast hb.2)).trans hy⟩

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
