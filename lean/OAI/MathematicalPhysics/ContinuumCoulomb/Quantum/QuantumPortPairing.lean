import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridNeighborsFour
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCornerPatch

namespace OAI

/-! Four distinct ports have the crossing pairing or one of the two corner pairings. -/

namespace ContinuumCoulomb

def qmaPortPairing (f : Fin 4 → Fin 4) : Finset (Sym2 (Fin 4)) :=
  {s(f 0,f 1),s(f 2,f 3)}

def qmaCrossPortPairing : Finset (Sym2 (Fin 4)) := {s(0,2),s(1,3)}
def qmaCornerPortPairing (mode : Bool) : Finset (Sym2 (Fin 4)) :=
  {s(qmaCornerPatchLeft mode 0,qmaCornerPatchRight mode 0),
   s(qmaCornerPatchLeft mode 1,qmaCornerPatchRight mode 1)}

theorem qmaPortPairing_classify (f : Fin 4 → Fin 4) (hf : Function.Injective f) :
    qmaPortPairing f = qmaCrossPortPairing ∨
      qmaPortPairing f = qmaCornerPortPairing false ∨
      qmaPortPairing f = qmaCornerPortPairing true := by
  have h01 : f 0 ≠ f 1 := fun h => (by decide : (0 : Fin 4) ≠ 1) (hf h)
  have h02 : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (hf h)
  have h03 : f 0 ≠ f 3 := fun h => (by decide : (0 : Fin 4) ≠ 3) (hf h)
  have h12 : f 1 ≠ f 2 := fun h => (by decide : (1 : Fin 4) ≠ 2) (hf h)
  have h13 : f 1 ≠ f 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (hf h)
  have h23 : f 2 ≠ f 3 := fun h => (by decide : (2 : Fin 4) ≠ 3) (hf h)
  unfold qmaPortPairing
  generalize ha : f 0 = a at *
  generalize hb : f 1 = b at *
  generalize hc : f 2 = c at *
  generalize hd : f 3 = d at *
  fin_cases a <;> fin_cases b <;> try contradiction
  all_goals (fin_cases c <;> try contradiction)
  all_goals (fin_cases d <;> first | contradiction | decide)

end ContinuumCoulomb

end OAI
