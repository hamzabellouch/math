import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPhysicalCells
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarListData
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarRouteRealization

namespace OAI

/-! The actual merged crossing output has a bounded, simple planar route family.
Each route uses at most twenty nearest-neighbor grid steps. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def crossingPlanarList (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2) :
    QMAPlanarListData (P.crossingOutput N hD).merge where
  position := P.crossingPosition N D
  position_injective := P.crossingPosition_injective N D
  path e := (P.mergedOutputRoute N hD havoid e).path
  length e := (P.mergedOutputRoute N hD havoid e).length_bounds.1
  first e := (P.mergedOutputRoute N hD havoid e).endpoints.1.trans
    (congrArg some (P.mergedOutputRoute_spec N hD havoid e).2.2.1)
  last e := (P.mergedOutputRoute N hD havoid e).endpoints.2.trans
    (congrArg some (P.mergedOutputRoute_spec N hD havoid e).2.2.2)
  simple e := (P.mergedOutputRoute N hD havoid e).simple
    (P.mergedOutputRoute_spec N hD havoid e).2.1
  step e := (P.mergedOutputRoute N hD havoid e).chain
    (P.mergedOutputRoute_spec N hD havoid e).2.1
  positive e z hz := by
    have hs := P.mergedOutputRoute_spec N hD havoid e
    apply (P.mergedOutputRoute N hD havoid e).path_positive ?_ ?_ hz
    · rw [hs.2.2.1]
      exact P.crossingPosition_positive hpositive N D _
    · rw [hs.2.2.2]
      exact P.crossingPosition_positive hpositive N D _
  avoids e v := P.mergedOutputRoute_avoids N hD havoid e v
  disjoint e f hef := P.mergedOutputRoute_disjoint N hD havoid e f hef

def crossingPlanarRoute (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2) :=
  (P.crossingPlanarList N hD havoid hpositive).toRoute

theorem crossingPlanarRoute_length (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)
    (e : (P.crossingOutput N hD).merge.Edge) :
    (P.crossingPlanarRoute N hD havoid hpositive).length e ≤ 20 := by
  change (P.mergedOutputRoute N hD havoid e).path.length-1 ≤ 20
  have h := (P.mergedOutputRoute N hD havoid e).length_bounds.2
  omega

theorem crossingPlanarList_path_bounded (N : ℚ) {D X Y : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y)
    (e : (P.crossingOutput N hD).merge.Edge) {z : ℕ × ℕ}
    (hz : z ∈ (P.mergedOutputRoute N hD havoid e).path) : z.1 < 32*X ∧ z.2 < 32*Y := by
  have hs := P.mergedOutputRoute_spec N hD havoid e
  apply (P.mergedOutputRoute N hD havoid e).path_bounded ?_ ?_ hz
  · rw [hs.2.2.1]
    exact P.crossingPosition_bounded hsource hpath N D _
  · rw [hs.2.2.2]
    exact P.crossingPosition_bounded hsource hpath N D _

theorem crossingPlanarRoute_bounded (N : ℚ) {D X Y : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)
    (hsource : ∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y)
    (hpath : ∀ e k, k ≤ P.length e → (P.point e k).1 < X ∧ (P.point e k).2 < Y) :
    (P.crossingPlanarRoute N hD havoid hpositive).Bounded (32*X) (32*Y) := by
  refine ⟨P.crossingPosition_bounded hsource hpath N D,?_⟩
  intro e k hk
  let L := P.crossingPlanarList N hD havoid hpositive
  change (L.point e k).1 < 32*X ∧ (L.point e k).2 < 32*Y
  apply P.crossingPlanarList_path_bounded N hD havoid hsource hpath e
  have hlen := L.length e
  exact L.point_mem e (by change k ≤ (L.path e).length-1 at hk; omega)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
