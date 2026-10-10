import OAI.Geometry.CylinderCovering.Radial.PairedSweepDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.RadialPairedSweep

def join {N : ℕ} (U L : Fin N → TriangularCovering.TriCylinder) :
    Fin (2 * N) → TriangularCovering.TriCylinder :=
  (Fin.append U L) ∘ Fin.cast (two_mul N)

def upperIndex {N : ℕ} (i : Fin N) : Fin (2 * N) :=
  Fin.cast (two_mul N).symm (Fin.castAdd N i)

def lowerIndex {N : ℕ} (i : Fin N) : Fin (2 * N) :=
  Fin.cast (two_mul N).symm (Fin.natAdd N i)

end CylinderCovering.RadialPairedSweep

end

end OAI
