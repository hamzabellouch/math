import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellRouteCatalog
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortCellPositive

namespace OAI

/-! Only 140 explicit catalog routes need be tested for a physical edge: the
seventy oriented routes in each endpoint cell. This supplies a fixed finite
search space for the literal planar-route compiler. -/

namespace ContinuumCoulomb

def QMACellRouteBody.cell : QMACellRouteBody → ℕ × ℕ
  | .ray p _ => p
  | .pair p _ => p
  | .patch p _ => p
  | .corridor p _ _ _ => p

def qmaCellBodies (p : ℕ × ℕ) : List QMACellRouteBody :=
  (List.finRange 4).map (.ray p) ++ (List.finRange 6).map (.pair p) ++
    (List.finRange 9).map (.patch p) ++
      (List.finRange 4).flatMap (fun a =>
        [.corridor p a false false,.corridor p a false true,
         .corridor p a true false,.corridor p a true true])

def qmaCellRoutes (p : ℕ × ℕ) : List QMACellRoute :=
  (qmaCellBodies p).flatMap (fun B => [⟨B,false⟩,⟨B,true⟩])

def qmaRouteCandidates (x y : ℕ × ℕ) : List QMACellRoute :=
  qmaCellRoutes (qmaPointCell x) ++ qmaCellRoutes (qmaPointCell y)

theorem qmaCellBodies_complete (B : QMACellRouteBody) : B ∈ qmaCellBodies B.cell := by
  cases B with
  | ray p a => simp [qmaCellBodies,QMACellRouteBody.cell]
  | pair p a => simp [qmaCellBodies,QMACellRouteBody.cell]
  | patch p a => simp [qmaCellBodies,QMACellRouteBody.cell]
  | corridor p a b c => cases b <;> cases c <;> simp [qmaCellBodies,QMACellRouteBody.cell]

theorem qmaCellRoutes_complete (R : QMACellRoute) : R ∈ qmaCellRoutes R.body.cell := by
  apply List.mem_flatMap.mpr
  refine ⟨R.body,qmaCellBodies_complete R.body,?_⟩
  rcases R with ⟨B,b⟩
  cases b <;> simp

theorem qmaCellBodies_length (p : ℕ × ℕ) : (qmaCellBodies p).length = 35 := by
  simp [qmaCellBodies,List.length_flatMap]

theorem qmaCellRoutes_length (p : ℕ × ℕ) : (qmaCellRoutes p).length = 70 := by
  simp [qmaCellRoutes,List.length_flatMap,qmaCellBodies_length]

theorem qmaRouteCandidates_length (x y : ℕ × ℕ) : (qmaRouteCandidates x y).length = 140 := by
  simp [qmaRouteCandidates,qmaCellRoutes_length]

theorem QMACellRouteBody.source_cell (B : QMACellRouteBody) : qmaPointCell B.source = B.cell := by
  cases B with
  | ray p a => exact qmaPointCell_center p
  | pair p e => exact qmaPointCell_port p (qmaCellPairLeft e)
  | patch p e =>
    apply Prod.ext <;> fin_cases e <;>
      simp [QMACellRouteBody.source,QMACellRouteBody.cell,qmaPointCell,qmaPatchTranslate,
        qmaCrossingPatchLeft,qmaCrossingPatchVertex,Nat.add_div]
  | corridor p a b c =>
    have h : (qmaLocalPort b a).1 < 32 ∧ (qmaLocalPort b a).2 < 32 := by
      cases b <;> fin_cases a <;> decide
    exact qmaCellTranslate_cell p _ h

theorem qmaRouteCandidates_complete (R : QMACellRoute) : R ∈ qmaRouteCandidates R.source R.target := by
  have h := qmaCellRoutes_complete R
  have hc : R.body.cell = qmaPointCell R.source ∨ R.body.cell = qmaPointCell R.target := by
    rcases R with ⟨B,b⟩
    cases b
    · exact Or.inl B.source_cell.symm
    · exact Or.inr B.source_cell.symm
  rcases hc with hc | hc
  · apply List.mem_append_left
    rwa [hc] at h
  · apply List.mem_append_right
    rwa [hc] at h

end ContinuumCoulomb

end OAI
