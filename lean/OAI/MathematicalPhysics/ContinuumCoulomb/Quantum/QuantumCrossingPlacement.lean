import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingMove
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortCrossingSelection

namespace OAI

/-! Injective physical placement for every spin after simultaneous crossing removal. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def movedPosition (N : ℚ) (D : ℕ) (v : Fin (P.finishedGraph N D).n) : ℕ × ℕ :=
  qmaCrossingMove P.IsCrossing (P.finishedPosition N D v)

theorem movedPosition_injective (N : ℚ) (D : ℕ) : Function.Injective (P.movedPosition N D) := by
  intro v w h
  apply (P.toEmbedding.iterate N D).position_injective
  exact qmaCrossingMove_injective P.IsCrossing (P.iterate_position_kind N D v)
    (P.iterate_position_kind N D w) h

theorem movedPosition_site (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (c : P.Crossing) (a : Fin 4) :
    P.movedPosition N D (P.crossingSite N hD c a) = qmaInnerPort c.val a := by
  unfold movedPosition
  rw [P.crossingSite_spec,qmaCrossingMove_port,ite_eq_left (P.mem_crossingCells.mp c.property)]

def freshCrossingPosition (i : Fin P.crossingCells.card) (b : Fin 2) : ℕ × ℕ :=
  qmaGadgetAncilla (P.crossingCell i).val b

theorem freshCrossingPosition_injective : Function.Injective
    (fun x : Fin P.crossingCells.card × Fin 2 => P.freshCrossingPosition x.1 x.2) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have he : ((P.crossingCell i).val,a) = ((P.crossingCell j).val,b) := qmaGadgetAncilla_injective h
  have hc : P.crossingCell i = P.crossingCell j :=
    Subtype.ext (congrArg (fun z : (ℕ × ℕ) × Fin 2 => z.1) he)
  have hij : i = j := P.crossingCells.equivFin.symm.injective hc
  have hab : a = b := congrArg (fun z : (ℕ × ℕ) × Fin 2 => z.2) he
  exact Prod.ext hij hab

theorem freshCrossingPosition_ne_old (N : ℚ) (D : ℕ) (i : Fin P.crossingCells.card) (a : Fin 2)
    (v : Fin (P.finishedGraph N D).n) : P.freshCrossingPosition i a ≠ P.movedPosition N D v :=
  qmaGadgetAncilla_ne_moved P.IsCrossing (P.crossingCell i).val a (P.iterate_position_kind N D v)

def crossingPosition (N : ℚ) (D : ℕ) :
    Fin ((P.finishedGraph N D).n+P.crossingCells.card*2) → ℕ × ℕ :=
  fun v => Sum.elim (P.movedPosition N D) (fun x => P.freshCrossingPosition x.1 x.2)
    ((vertexEquiv (P.finishedGraph N D).n P.crossingCells.card).symm v)

@[simp] theorem crossingPosition_old (N : ℚ) (D : ℕ) (v : Fin (P.finishedGraph N D).n) :
    P.crossingPosition N D (old _ _ v) = P.movedPosition N D v := by
  simp [crossingPosition,old]

@[simp] theorem crossingPosition_fresh (N : ℚ) (D : ℕ) (i : Fin P.crossingCells.card) (a : Fin 2) :
    P.crossingPosition N D (fresh _ _ i a) = P.freshCrossingPosition i a := by
  simp [crossingPosition,fresh]

theorem crossingPosition_injective (N : ℚ) (D : ℕ) : Function.Injective (P.crossingPosition N D) := by
  intro x y h
  obtain ⟨x,rfl⟩ := (vertexEquiv (P.finishedGraph N D).n P.crossingCells.card).surjective x
  obtain ⟨y,rfl⟩ := (vertexEquiv (P.finishedGraph N D).n P.crossingCells.card).surjective y
  simp only [crossingPosition,Equiv.symm_apply_apply] at h
  apply (vertexEquiv _ _).congr_arg
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (P.movedPosition_injective N D h)
    | inr y => exact (P.freshCrossingPosition_ne_old N D y.1 y.2 x h.symm).elim
  | inr x =>
    cases y with
    | inl y => exact (P.freshCrossingPosition_ne_old N D x.1 x.2 y h).elim
    | inr y => exact congrArg Sum.inr (P.freshCrossingPosition_injective h)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
