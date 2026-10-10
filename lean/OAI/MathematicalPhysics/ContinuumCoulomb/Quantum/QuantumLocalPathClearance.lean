import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHalfCorridor

namespace OAI

/-! Exact endpoint clearance inside one cell. These finite facts separate
external corridors from the rays, ordinary pairs and nine gadget paths. -/

namespace ContinuumCoulomb

def qmaLocalPhysicalSites (cross : Bool) : Finset (ℕ × ℕ) :=
  if cross then {(16,16),(10,16),(16,22),(22,16),(16,10),(14,18),(18,14)}
  else {(16,16),(23,16),(16,23),(9,16),(16,9)}

theorem qmaHalfCorridor_sites (cross : Bool) (a : Fin 4) :
    Disjoint ((qmaHalfCorridorPath cross a).drop 1).toFinset (qmaLocalPhysicalSites cross) := by
  cases cross <;> fin_cases a <;> decide

theorem qmaCellRay_sites (a : Fin 4) :
    Disjoint (((qmaCellRayPath a).drop 1).dropLast).toFinset (qmaLocalPhysicalSites false) := by
  fin_cases a <;> decide

theorem qmaLocalPatch_sites (e : Fin 9) :
    Disjoint (((qmaLocalPatchPath e).drop 1).dropLast).toFinset (qmaLocalPhysicalSites true) := by
  fin_cases e <;> decide

theorem qmaCellPair_half (e : Fin 6) (a : Fin 4) :
    Disjoint (((qmaCellPairPath e).drop 1).dropLast).toFinset (qmaHalfCorridorPath false a).toFinset := by
  fin_cases e <;> fin_cases a <;> decide

theorem qmaCellRay_half (e a : Fin 4) :
    Disjoint (((qmaCellRayPath e).drop 1).dropLast).toFinset (qmaHalfCorridorPath false a).toFinset := by
  fin_cases e <;> fin_cases a <;> decide

theorem qmaLocalPatch_half (e : Fin 9) (a : Fin 4) :
    Disjoint (((qmaLocalPatchPath e).drop 1).dropLast).toFinset (qmaHalfCorridorPath true a).toFinset := by
  fin_cases e <;> fin_cases a <;> decide

theorem qmaLocalPatch_bounded (e : Fin 9) :
    ∀ p ∈ qmaLocalPatchPath e, 10 ≤ p.1 ∧ p.1 ≤ 22 ∧ 10 ≤ p.2 ∧ p.2 ≤ 22 := by
  fin_cases e <;> decide

end ContinuumCoulomb

end OAI
