import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPatch

namespace OAI

/-! The two noncrossing pairings of four boundary ports use disjoint corner paths. -/

namespace ContinuumCoulomb

def qmaCornerPatchEdge (mode : Bool) (a : Fin 2) : Fin 9 :=
  if mode then ![6,8] a else ![5,7] a

def qmaCornerPatchLeft (mode : Bool) (a : Fin 2) : Fin 4 :=
  if mode then ![1,3] a else ![0,2] a

def qmaCornerPatchRight (mode : Bool) (a : Fin 2) : Fin 4 :=
  if mode then ![2,0] a else ![1,3] a

def qmaCornerPatchPath (mode : Bool) (a : Fin 2) : List (ℕ × ℕ) :=
  qmaCrossingPatchPath (qmaCornerPatchEdge mode a)

theorem qmaCornerPatch_endpoints (mode : Bool) (a : Fin 2) :
    (qmaCornerPatchPath mode a).head? =
        some (qmaCrossingPatchVertex ((qmaCornerPatchLeft mode a).castLE (by decide))) ∧
      (qmaCornerPatchPath mode a).getLast? =
        some (qmaCrossingPatchVertex ((qmaCornerPatchRight mode a).castLE (by decide))) := by
  cases mode <;> fin_cases a <;> decide

theorem qmaCornerPatch_chain (mode : Bool) (a : Fin 2) :
    (qmaCornerPatchPath mode a).IsChain
      (fun p q => Nat.dist p.1 q.1+Nat.dist p.2 q.2 = 1) :=
  qmaCrossingPatch_chain _

theorem qmaCornerPatch_simple (mode : Bool) (a : Fin 2) :
    (qmaCornerPatchPath mode a).Nodup := qmaCrossingPatch_simple _

theorem qmaCornerPatch_disjoint (mode : Bool) :
    Disjoint (qmaCornerPatchPath mode 0).toFinset (qmaCornerPatchPath mode 1).toFinset := by
  cases mode <;> decide

theorem qmaCornerPatch_length (mode : Bool) (a : Fin 2) :
    (qmaCornerPatchPath mode a).length = 13 := by
  cases mode <;> fin_cases a <;> decide

theorem qmaCornerPatch_bounded (mode : Bool) (a : Fin 2) :
    ∀ p ∈ qmaCornerPatchPath mode a, p.1 ≤ 12 ∧ p.2 ≤ 12 :=
  qmaCrossingPatch_bounded _

end ContinuumCoulomb

end OAI
