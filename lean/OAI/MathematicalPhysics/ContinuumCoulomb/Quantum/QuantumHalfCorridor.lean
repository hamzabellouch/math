import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellPathTemplates
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumInnerPorts

namespace OAI

/-! Each external corridor splits into two paths contained in their own cells,
joined by one unit edge. These paths meet the internal templates only at ports. -/

namespace ContinuumCoulomb

def qmaHalfCorridorPath (cross : Bool) : Fin 4 → List (ℕ × ℕ) :=
  if cross then ![
    [(22,16),(23,16),(24,16),(25,16),(26,16),(27,16),(28,16),(29,16),(30,16),(31,16)],
    [(16,22),(16,23),(16,24),(16,25),(16,26),(16,27),(16,28),(16,29),(16,30),(16,31)],
    [(10,16),(9,16),(8,16),(7,16),(6,16),(5,16),(4,16),(3,16),(2,16),(1,16),(0,16)],
    [(16,10),(16,9),(16,8),(16,7),(16,6),(16,5),(16,4),(16,3),(16,2),(16,1),(16,0)]] else ![
    [(23,16),(24,16),(25,16),(26,16),(27,16),(28,16),(29,16),(30,16),(31,16)],
    [(16,23),(16,24),(16,25),(16,26),(16,27),(16,28),(16,29),(16,30),(16,31)],
    [(9,16),(8,16),(7,16),(6,16),(5,16),(4,16),(3,16),(2,16),(1,16),(0,16)],
    [(16,9),(16,8),(16,7),(16,6),(16,5),(16,4),(16,3),(16,2),(16,1),(16,0)]]

def qmaLocalPatchPath (e : Fin 9) : List (ℕ × ℕ) :=
  (qmaCrossingPatchPath e).map (fun z => (10+z.1,10+z.2))

def qmaCellBoundary : Fin 4 → ℕ × ℕ := ![(31,16),(16,31),(0,16),(16,0)]

def qmaLocalPort (cross : Bool) (a : Fin 4) : ℕ × ℕ :=
  if cross then qmaInnerPort (0,0) a else qmaCellPort a

theorem qmaHalfCorridor_endpoints (cross : Bool) (a : Fin 4) :
    (qmaHalfCorridorPath cross a).head? = some (qmaLocalPort cross a) ∧
    (qmaHalfCorridorPath cross a).getLast? = some (qmaCellBoundary a) := by
  cases cross <;> fin_cases a <;> decide

theorem qmaHalfCorridor_length (cross : Bool) (a : Fin 4) :
    9 ≤ (qmaHalfCorridorPath cross a).length ∧ (qmaHalfCorridorPath cross a).length ≤ 11 := by
  cases cross <;> fin_cases a <;> decide

theorem qmaHalfCorridor_chain (cross : Bool) (a : Fin 4) :
    (qmaHalfCorridorPath cross a).IsChain
      (fun p q => Nat.dist p.1 q.1+Nat.dist p.2 q.2 = 1) := by
  cases cross <;> fin_cases a <;> decide

theorem qmaHalfCorridor_simple (cross : Bool) (a : Fin 4) :
    (qmaHalfCorridorPath cross a).Nodup := by
  cases cross <;> fin_cases a <;> decide

theorem qmaHalfCorridor_bounded (cross : Bool) (a : Fin 4) :
    ∀ p ∈ qmaHalfCorridorPath cross a, p.1 < 32 ∧ p.2 < 32 := by
  cases cross <;> fin_cases a <;> decide

theorem qmaHalfCorridor_disjoint (cross : Bool) (a b : Fin 4) (hab : a ≠ b) :
    Disjoint (qmaHalfCorridorPath cross a).toFinset (qmaHalfCorridorPath cross b).toFinset := by
  cases cross <;> fin_cases a <;> fin_cases b <;> first | exact (hab rfl).elim | decide

theorem qmaHalfCorridor_pair (a : Fin 4) (e : Fin 6) :
    Disjoint ((qmaHalfCorridorPath false a).drop 1).toFinset (qmaCellPairPath e).toFinset := by
  fin_cases a <;> fin_cases e <;> decide

theorem qmaHalfCorridor_ray (a b : Fin 4) :
    Disjoint ((qmaHalfCorridorPath false a).drop 1).toFinset (qmaCellRayPath b).toFinset := by
  fin_cases a <;> fin_cases b <;> decide

theorem qmaHalfCorridor_patch (a : Fin 4) (e : Fin 9) :
    Disjoint ((qmaHalfCorridorPath true a).drop 1).toFinset (qmaLocalPatchPath e).toFinset := by
  fin_cases a <;> fin_cases e <;> decide

end ContinuumCoulomb

end OAI
