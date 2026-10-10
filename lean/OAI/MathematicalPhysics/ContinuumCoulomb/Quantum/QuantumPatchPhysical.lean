import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingsGraph
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPatch
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingSize

namespace OAI

/-! The nine ordinary physical gadget edges are exactly the fixed patch edges,
with only the west-south perimeter edge oriented in reverse. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph

def qmaPatchPhysicalVertex {n r : ℕ} (site : Fin r → Fin 4 → Fin n) (i : Fin r) : Fin 6 → Fin (n+r*2) :=
  ![old n r (site i 0),old n r (site i 1),old n r (site i 2),old n r (site i 3),
    fresh n r i 0,fresh n r i 1]

def qmaPatchPhysicalEdge {ν : Type*} {r : ℕ} (i : Fin r) : Fin 9 → QMACrossingsGraphEdge ν r :=
  ![.inr (.inl i),.inr (.inr (i,0)),.inr (.inr (i,1)),.inr (.inr (i,2)),.inr (.inr (i,3)),
    .inl (.inr (i,0)),.inl (.inr (i,2)),.inl (.inr (i,3)),.inl (.inr (i,1))]

def qmaPatchSource (e : Fin 9) : Fin 6 := if e = 8 then qmaCrossingPatchRight e else qmaCrossingPatchLeft e

def qmaPatchTarget (e : Fin 9) : Fin 6 := if e = 8 then qmaCrossingPatchLeft e else qmaCrossingPatchRight e

theorem qmaPatchPhysical_left {ν : Type*} {n r : ℕ} (left : ν → Fin n)
    (site : Fin r → Fin 4 → Fin n) (i : Fin r) (e : Fin 9) :
    qmaParallelGraphLeft (qmaCrossingsBaseLeft left site) site (qmaPatchPhysicalEdge i e) =
      qmaPatchPhysicalVertex site i (qmaPatchSource e) := by
  fin_cases e <;> rfl

theorem qmaPatchPhysical_right {ν : Type*} {n r : ℕ} (right : ν → Fin n)
    (site : Fin r → Fin 4 → Fin n) (i : Fin r) (e : Fin 9) :
    qmaParallelGraphRight (qmaCrossingsBaseRight right site) (fun _ => qmaCrossingMember)
      (qmaPatchPhysicalEdge i e) = qmaPatchPhysicalVertex site i (qmaPatchTarget e) := by
  fin_cases e <;> rfl

end ContinuumCoulomb

end

end OAI
