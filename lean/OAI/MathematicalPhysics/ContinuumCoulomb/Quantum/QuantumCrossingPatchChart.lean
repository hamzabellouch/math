import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPlacement
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPatchPhysical

namespace OAI

/-! Each selected gadget's six physical spins occupy exactly the six vertices
of the explicit translated planar patch. -/

noncomputable section
namespace ContinuumCoulomb
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem crossingPosition_patchVertex (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (i : Fin P.crossingCells.card) (v : Fin 6) :
    P.crossingPosition N D (qmaPatchPhysicalVertex (P.crossingSiteFin N hD) i v) =
      qmaPatchTranslate (P.crossingCell i).val (qmaCrossingPatchVertex v) := by
  fin_cases v <;> simp [qmaPatchPhysicalVertex,P.crossingPosition_old,P.crossingPosition_fresh,
    crossingSiteFin,movedPosition_site,freshCrossingPosition,qmaInnerPort,qmaGadgetAncilla,
    qmaPatchDirection,qmaPatchTranslate,qmaCrossingPatchVertex,Nat.add_assoc]

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
