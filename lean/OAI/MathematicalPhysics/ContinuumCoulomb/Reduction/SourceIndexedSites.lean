import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceGraphIndex
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourceNuclearProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PrefactorSourceCalibration

namespace OAI

/-! The literal nuclear program's planar sites, expressed in the same
index type as its finite Hubbard graph. -/

noncomputable section
namespace ContinuumCoulomb.SourceNuclearProgram
open SourceMetadataProgram ContactMediator

def contactSpacing (c : ℚ) (k : ℕ) (d : BinaryHeisenberg) : ℚ :=
  AutomaticCalibration.spacing c k (CalibrationMesh.base (SourceContactProgram.size d))

def contactLengths (rho C : ℕ) (eps c : ℚ) (s p k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) : GlobalEdge (geometricSource s d hd) → ℚ :=
  CalibratedContactProgram.graphLengths rho eps c k A B
    (CalibrationMesh.base (SourceContactProgram.size d))
    (PrefactorCalibration.precision C (SourceContactProgram.size d^p))
    (geometricSource s d hd)
    (PrefactorSourceContactProgram.weights (CalibrationMesh.prefactor rho) s d hd)

def rawSites (rho C : ℕ) (eps c : ℚ) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) : GlobalSite (geometricSource s d hd) → ℚ×ℚ :=
  ContactCalibratedGeometry.position (geometricSource s d hd) (SourceContactProgram.size d^h)
    (contactSpacing c k d) (contactLengths rho C eps c s p k A B d hd)

def indexedCoordinates (rho C : ℕ) (eps c : ℚ) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (SourcePositiveProgram.output s d).vertices=m+1) : Fin (m+1) → ℚ×ℚ :=
  fun i => rawSites rho C eps c s p h k A B d hd
    ((SourcePositiveProgram.indexedSites s d hd hm).symm i)

theorem sites_eq_indexed (rho C : ℕ) (eps c : ℚ) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (SourcePositiveProgram.output s d).vertices=m+1) :
    sites rho C eps c s p h k A B d =
      List.ofFn (indexedCoordinates rho C eps c s p h k A B d hd hm) := by
  unfold sites
  rw [PrefactorSourceContactProgram.value_eq_array]
  exact (SourcePositiveProgram.indexedSites_ofFn s d hd hm
    (rawSites rho C eps c s p h k A B d hd)).symm

theorem indexed_position (rho C : ℕ) (eps c : ℚ) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ}
    (hm : (SourcePositiveProgram.output s d).vertices=m+1) (i : Fin (m+1)) :
    PlanarForcingProgram.position (indexedCoordinates rho C eps c s p h k A B d hd hm i) =
      ContactCalibratedGeometry.point (geometricSource s d hd) (SourceContactProgram.size d^h)
        (contactSpacing c k d) (contactLengths rho C eps c s p k A B d hd)
        ((SourcePositiveProgram.indexedSites s d hd hm).symm i) := by
  exact ContactCalibratedGeometry.position_cast _ _ _ _ _

theorem lengths_scale (rho C : ℕ) (eps : ℚ) {c : ℚ} (hc : 0 < c) (s p k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) (e : GlobalEdge (geometricSource s d hd)) :
    (contactSpacing c k d:ℝ)*contactLengths rho C eps c s p k A B d hd e =
      PrefactorSourceContactProgram.nominalDistance rho (CalibrationMesh.prefactor rho) C eps c
        s p k A B d hd e :=
  PrefactorSourceContactProgram.graphLengths_scale rho (CalibrationMesh.prefactor rho) C eps hc
    s p k A B d hd e

end ContinuumCoulomb.SourceNuclearProgram

end

end OAI
