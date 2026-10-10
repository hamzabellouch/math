import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenRouteRealization
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumInflatedSeparation

namespace OAI

/-! A planar route family supplies the even physical subdivision data explicitly,
including its four-direction reserved leaf sites. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

structure QMAPlanarRouteData (G : QMARationalExchangeGraph) where
  length : G.Edge → ℕ
  length_pos : ∀ e, 0 < length e
  position : Fin G.n → ℕ × ℕ
  position_injective : Function.Injective position
  point : G.Edge → ℕ → ℕ × ℕ
  positive : ∀ e i, i ≤ length e → 0 < (point e i).1 ∧ 0 < (point e i).2
  first : ∀ e, point e 0 = position (G.left e)
  last : ∀ e, point e (length e) = position (G.right e)
  simple : ∀ e i j, i ≤ length e → j ≤ length e → point e i = point e j → i = j
  step : ∀ e i, i < length e → qmaSquareGrid.Adj (point e i) (point e (i+1))
  avoids : ∀ e i v, 0 < i → i < length e → point e i ≠ position v
  disjoint : ∀ e f i j, e ≠ f → 0 < i → i < length e → j ≤ length f → point e i ≠ point f j
  edges_disjoint : ∀ e f, e ≠ f → ∀ i j, i < length e → j < length f →
    ¬(point e i = point f j ∧ point e (i+1) = point f (j+1)) ∧
    ¬(point e i = point f (j+1) ∧ point e (i+1) = point f j)

namespace QMAPlanarRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)

def direction (e : G.Edge) : Fin 4 := qmaGridNeighborIndex (P.point e 0) (P.point e 1)

theorem direction_spec (e : G.Edge) :
    qmaGridNeighbor (P.point e 0) (P.direction e) = P.point e 1 :=
  qmaGridNeighborIndex_spec (P.positive e 0 (Nat.zero_le _)).1
    (P.positive e 0 (Nat.zero_le _)).2 (P.step e 0 (P.length_pos e))

def leaf (e : G.Edge) : ℕ × ℕ := qmaRouteLeaf (P.point e 0) (P.direction e)

theorem leaf_injective : Function.Injective P.leaf := by
  intro e f h
  by_contra hef
  have hp : (P.point e 0,P.direction e) = (P.point f 0,P.direction f) :=
    qmaRouteLeaf_injective h
  have h0 := congrArg Prod.fst hp
  have h1 := congrArg (fun z : (ℕ × ℕ) × Fin 4 => qmaGridNeighbor z.1 z.2) hp
  rw [P.direction_spec e,P.direction_spec f] at h1
  exact (P.edges_disjoint e f hef 0 0 (P.length_pos e) (P.length_pos f)).1 ⟨h0,h1⟩

theorem even_length (e : G.Edge) : 2*(4*P.length e-1)+2 = 8*P.length e := by
  have h := P.length_pos e
  omega

def toEven : QMAEvenRouteData G where
  work e := 4*P.length e-1
  position v := qmaLeafCenter (P.position v)
  position_injective := qmaLeafCenter_injective.comp P.position_injective
  point e := qmaInflatedPoint (P.point e)
  first e := by rw [qmaInflatedPoint_zero,P.first]
  last e := by rw [P.even_length,qmaInflatedPoint_last,P.last]
  simple e i j hi hj h := by
    rw [P.even_length] at hi hj
    exact qmaInflatedPoint_injective (P.point e) (P.positive e) (P.step e) (P.simple e) hi hj h
  step e i hi := by
    rw [P.even_length] at hi
    exact qmaInflatedPoint_step (P.point e) (P.step e) hi
  avoids e i v hi0 hi := by
    rw [P.even_length] at hi
    exact qmaInflatedPoint_avoids_vertex (P.point e) (P.positive e) (P.step e) (P.position v)
      (fun j hj0 hj => P.avoids e j v hj0 hj) hi0 hi
  disjoint e f i j hef hi0 hi hj := by
    rw [P.even_length] at hi
    rw [P.even_length] at hj
    exact qmaInflatedPoint_disjoint (P.point e) (P.point f) (P.positive e) (P.positive f)
      (P.step e) (P.step f) (fun a b ha0 ha hb => P.disjoint e f a b hef ha0 ha hb)
      (P.edges_disjoint e f hef) hi0 hi hj
  leaf := P.leaf
  leaf_injective := P.leaf_injective
  leaf_step e := by
    change qmaSquareGrid.Adj
      (qmaManhattanPoint (qmaLeafCenter (P.point e 0)) (qmaLeafCenter (P.point e 1)) 1) (P.leaf e)
    rw [qmaLeafCenter_point_first (P.positive e 0 (Nat.zero_le _)).1
      (P.positive e 0 (Nat.zero_le _)).2 (P.step e 0 (P.length_pos e))]
    exact qmaRouteLeaf_step _ _
  leaf_avoids e f k hk := by
    rw [P.even_length] at hk
    exact qmaRouteLeaf_avoids _ _ _ (qmaInflatedPoint_gridline (P.point f) (P.step f) hk)
  leaf_old e v := by
    apply qmaRouteLeaf_avoids
    left
    simp [qmaLeafCenter,Nat.add_mod]

end QMAPlanarRouteData
end ContinuumCoulomb

end

end OAI
