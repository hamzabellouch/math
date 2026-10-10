import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPatchPoints
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortPairing

namespace OAI

/-! The six possible ordinary-cell connections and four source rays. The two
opposite pairs are the only disjoint-port pair whose paths cross. -/

namespace ContinuumCoulomb

def qmaCellPairLeft : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def qmaCellPairRight : Fin 6 → Fin 4 := ![1,2,3,2,3,3]
def qmaCellPairPath : Fin 6 → List (ℕ × ℕ) := ![
  [(23,16),(23,17),(23,18),(23,19),(23,20),(23,21),(23,22),(23,23),(22,23),(21,23),(20,23),(19,23),(18,23),(17,23),(16,23)],
  [(23,16),(22,16),(21,16),(20,16),(19,16),(18,16),(17,16),(16,16),(15,16),(14,16),(13,16),(12,16),(11,16),(10,16),(9,16)],
  [(23,16),(23,15),(23,14),(23,13),(23,12),(23,11),(23,10),(23,9),(22,9),(21,9),(20,9),(19,9),(18,9),(17,9),(16,9)],
  [(16,23),(15,23),(14,23),(13,23),(12,23),(11,23),(10,23),(9,23),(9,22),(9,21),(9,20),(9,19),(9,18),(9,17),(9,16)],
  [(16,23),(16,22),(16,21),(16,20),(16,19),(16,18),(16,17),(16,16),(16,15),(16,14),(16,13),(16,12),(16,11),(16,10),(16,9)],
  [(9,16),(9,15),(9,14),(9,13),(9,12),(9,11),(9,10),(9,9),(10,9),(11,9),(12,9),(13,9),(14,9),(15,9),(16,9)]]

def qmaCellRayPath : Fin 4 → List (ℕ × ℕ) := ![
  [(16,16),(17,16),(18,16),(19,16),(20,16),(21,16),(22,16),(23,16)],
  [(16,16),(16,17),(16,18),(16,19),(16,20),(16,21),(16,22),(16,23)],
  [(16,16),(15,16),(14,16),(13,16),(12,16),(11,16),(10,16),(9,16)],
  [(16,16),(16,15),(16,14),(16,13),(16,12),(16,11),(16,10),(16,9)]]

def qmaCellPort : Fin 4 → ℕ × ℕ := ![(23,16),(16,23),(9,16),(16,9)]

theorem qmaCellPair_distinct (e : Fin 6) : qmaCellPairLeft e ≠ qmaCellPairRight e := by
  fin_cases e <;> decide

theorem qmaCellPair_complete (a b : Fin 4) (hab : a ≠ b) :
    ∃ e : Fin 6, (a = qmaCellPairLeft e ∧ b = qmaCellPairRight e) ∨
      (a = qmaCellPairRight e ∧ b = qmaCellPairLeft e) := by
  fin_cases a <;> fin_cases b <;> first | exact (hab rfl).elim | decide

theorem qmaCellPair_endpoints (e : Fin 6) :
    (qmaCellPairPath e).head? = some (qmaCellPort (qmaCellPairLeft e)) ∧
    (qmaCellPairPath e).getLast? = some (qmaCellPort (qmaCellPairRight e)) := by
  fin_cases e <;> decide

theorem qmaCellPair_length (e : Fin 6) : (qmaCellPairPath e).length = 15 := by
  fin_cases e <;> decide

theorem qmaCellPair_chain (e : Fin 6) : (qmaCellPairPath e).IsChain
    (fun p q => Nat.dist p.1 q.1+Nat.dist p.2 q.2 = 1) := by
  fin_cases e <;> decide

theorem qmaCellPair_simple (e : Fin 6) : (qmaCellPairPath e).Nodup := by
  fin_cases e <;> decide

theorem qmaCellPair_bounded (e : Fin 6) :
    ∀ p ∈ qmaCellPairPath e, 9 ≤ p.1 ∧ p.1 ≤ 23 ∧ 9 ≤ p.2 ∧ p.2 ≤ 23 := by
  fin_cases e <;> decide

theorem qmaCellPair_ports (e : Fin 6) :
    Disjoint ((qmaCellPairPath e).drop 1 |>.dropLast).toFinset
      (Finset.univ.image qmaCellPort) := by
  fin_cases e <;> decide

theorem qmaCellPair_disjoint (e f : Fin 6)
    (h00 : qmaCellPairLeft e ≠ qmaCellPairLeft f)
    (h01 : qmaCellPairLeft e ≠ qmaCellPairRight f)
    (h10 : qmaCellPairRight e ≠ qmaCellPairLeft f)
    (h11 : qmaCellPairRight e ≠ qmaCellPairRight f)
    (hc : ¬(e = 1 ∧ f = 4) ∧ ¬(e = 4 ∧ f = 1)) :
    Disjoint (qmaCellPairPath e).toFinset (qmaCellPairPath f).toFinset := by
  fin_cases e <;> fin_cases f <;>
    first | exact (h00 rfl).elim | exact (h01 rfl).elim |
      exact (h10 rfl).elim | exact (h11 rfl).elim |
      exact (hc.1 ⟨rfl,rfl⟩).elim | exact (hc.2 ⟨rfl,rfl⟩).elim | decide

theorem qmaCellRay_endpoints (a : Fin 4) :
    (qmaCellRayPath a).head? = some (16,16) ∧
    (qmaCellRayPath a).getLast? = some (qmaCellPort a) := by
  fin_cases a <;> decide

theorem qmaCellRay_length (a : Fin 4) : (qmaCellRayPath a).length = 8 := by
  fin_cases a <;> decide

theorem qmaCellRay_chain (a : Fin 4) : (qmaCellRayPath a).IsChain
    (fun p q => Nat.dist p.1 q.1+Nat.dist p.2 q.2 = 1) := by
  fin_cases a <;> decide

theorem qmaCellRay_simple (a : Fin 4) : (qmaCellRayPath a).Nodup := by
  fin_cases a <;> decide

theorem qmaCellRay_disjoint (a b : Fin 4) (hab : a ≠ b) :
    Disjoint ((qmaCellRayPath a).drop 1).toFinset (qmaCellRayPath b).toFinset := by
  fin_cases a <;> fin_cases b <;> first | exact (hab rfl).elim | decide

theorem qmaCellRay_bounded (a : Fin 4) :
    ∀ p ∈ qmaCellRayPath a, 9 ≤ p.1 ∧ p.1 ≤ 23 ∧ 9 ≤ p.2 ∧ p.2 ≤ 23 := by
  fin_cases a <;> decide

end ContinuumCoulomb

end OAI
