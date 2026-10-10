import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourceContactProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePositiveCorrectness
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceGeometryBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedContactCorrectness

namespace OAI

/-! The raw-source program has exactly the normalized lattice geometry and
the full three-stage positive weights, including their original order. -/

noncomputable section
namespace ContinuumCoulomb.SourceContactProgram
open ContactMediator

def weights (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    GlobalEdge (SourceMetadataProgram.geometricSource s d hd) → ℚ :=
  (MediatorIteration.finalGraph (SourceMetadataProgram.geometricSource s d hd).bonds
    (SourcePositiveProgram.sourceBound s d) (SourceMetadataProgram.size d ^ s)).weight

theorem coordinates_eq (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    d.coordinate = List.ofFn (SourceMetadataProgram.geometricSource s d hd).coordinate := by
  exact (List.ofFn_get d.coordinate).symm

theorem signedBonds_eq (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (SourcePositiveProgram.normalized s d).2 =
      (SourceMetadataProgram.geometricSource s d hd).bonds.toList := by
  rw [SourcePositiveProgram.normalized_literal s d hd]
  rfl

theorem weights_eq (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2) =
      List.ofFn (weights s d hd) := by
  rw [SourcePositiveProgram.bonds_eq s d hd]
  simp only [MediatorIteration.Bonds.toList,List.map_ofFn,Function.comp_def]
  rfl

theorem input_eq_graphInput (s p h : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    input s p h d = CalibratedContactProgram.graphInput
      (SourceMetadataProgram.geometricSource s d hd) (size d) (size d ^ p) (size d ^ h)
        (weights s d hd) := by
  unfold input CalibratedContactProgram.graphInput
  rw [coordinates_eq s d hd,signedBonds_eq s d hd,weights_eq s d hd]

theorem value_eq_array (rho : ℕ) (ε c : ℚ) (s p h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) :
    value rho ε c s p h k A B d = List.ofFn (fun x =>
      ContactCalibratedGeometry.position (SourceMetadataProgram.geometricSource s d hd)
        (size d ^ h) (AutomaticCalibration.spacing c k (size d))
        (CalibratedContactProgram.graphLengths rho ε c k A B (size d) (size d ^ p)
          (SourceMetadataProgram.geometricSource s d hd) (weights s d hd)) x) := by
  unfold value
  rw [input_eq_graphInput]
  exact CalibratedContactProgram.value_graphInput _ _ _ _ _ _ _ _ _ _ _

end ContinuumCoulomb.SourceContactProgram

end

end OAI
