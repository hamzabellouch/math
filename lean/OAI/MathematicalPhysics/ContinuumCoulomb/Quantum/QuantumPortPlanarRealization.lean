import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPlanarRoutes
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarDegree

namespace OAI

/-! Actual planarization and nearest-neighbor realization of the completed port
graph, using eighty-one fixed subdivision layers after the crossing layer. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem planar_realize {N : ℚ} (hN : 0 < N) {D X Y : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y) :
    ∃ (H : QMARationalExchangeGraph) (position : Fin H.n → ℕ × ℕ),
      Function.Injective position ∧
      (∀ v, (position v).1 < 256*X ∧ (position v).2 < 256*Y) ∧
      (∀ e, qmaSquareGrid.Adj (position (H.left e)) (position (H.right e))) ∧
      (∀ v, qmaGraphDegree H.left H.right v ≤ 4) ∧
      H.n+Fintype.card H.Edge ≤ 5^81*((P.crossingOutput N hD).merge.n+
        Fintype.card (P.crossingOutput N hD).merge.Edge) ∧
      |H.energy-G.energy| ≤ ((D+82:ℕ):ℝ)/(N:ℝ) := by
  let R := P.crossingPlanarRoute N hD havoid hpositive
  have hlen : ∀ e, R.length e ≤ 20 := P.crossingPlanarRoute_length N hD havoid hpositive
  have hbox : R.Bounded (32*X) (32*Y) :=
    P.crossingPlanarRoute_bounded N hD havoid hpositive hsource hpath
  obtain ⟨H,pos,hinj,hbounds,hgrid,hdegree,hsize,herr⟩ :=
    R.realize hN (by decide : 3 ≤ 4) hlen hbox R.degree_le_four
  refine ⟨H,pos,hinj,?_,hgrid,hdegree,hsize,?_⟩
  · simpa only [← Nat.mul_assoc] using hbounds
  · have hcross := P.mergedOutput_energy_error hN hD
    calc
      _ ≤ |H.energy-(P.crossingOutput N hD).merge.energy|+
          |(P.crossingOutput N hD).merge.energy-G.energy| := abs_sub_le _ _ _
      _ ≤ ((4*20+1:ℕ):ℝ)/(N:ℝ)+((D+1:ℕ):ℝ)/(N:ℝ) := add_le_add herr hcross
      _ = _ := by push_cast; ring

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
