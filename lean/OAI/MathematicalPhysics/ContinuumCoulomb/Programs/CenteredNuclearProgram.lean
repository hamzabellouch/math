import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CenteredGaussProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearCoordinateOutput

namespace OAI

/-! The complete finite rational nucleus list, generated from the actual
rectangular cell bounds, numerically transported, and serialized using the
continuum promise's own position codec. -/

open scoped NNReal
namespace ContinuumCoulomb.CenteredNuclearProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := TransformedGauss.Environment×CenteredGaussLabels.Radii
def inputCode : Input → List Bool :=
  prodCode TransformedGauss.environmentCode CenteredGaussLabels.radiiCode

noncomputable def nuclei (rho U C K : ℕ) (x : Input) : List BinaryPosition :=
  NuclearCoordinateOutput.positions
    (TransformedGauss.nodes rho U C K (x.1,CenteredGaussLabels.labels x.2))

noncomputable opaque argumentsProgram : Procedure inputCode TransformedGauss.listInputCode
    (fun x => (x.1,CenteredGaussLabels.labels x.2)) :=
  (Procedure.first _ _).pair (CenteredGaussLabels.labelsProgram.comp (Procedure.second _ _))

noncomputable opaque program (rho U C K : ℕ) : Procedure inputCode
    (BinaryEncoding.list binaryPositionCodec).encode (nuclei rho U C K) :=
  NuclearCoordinateOutput.positionsProgram.comp
    ((TransformedGauss.listProgram rho U C K).comp argumentsProgram)

noncomputable def certificate (rho U C K : ℕ) : Turing.TM2ComputableInPolyTime inputCode
    (BinaryEncoding.list binaryPositionCodec).encode (nuclei rho U C K) :=
  (program rho U C K).toTM2

theorem nuclei_length (rho U C K : ℕ) (x : Input) :
    (nuclei rho U C K x).length =
      8*((2*x.2.1+1)*(2*x.2.2.1+1)*(2*x.2.2.2+1)) := by
  rw [nuclei,NuclearCoordinateOutput.positions_length,TransformedGauss.nodes_length,
    CenteredGaussLabels.labels_length]

theorem nuclei_valid (rho U C K : ℕ) (x : Input) {p : BinaryPosition}
    (hp : p ∈ nuclei rho U C K x) : p.Valid :=
  NuclearCoordinateOutput.positions_valid _ hp

theorem nuclei_nonempty (rho U C K : ℕ) (x : Input) : 0 < (nuclei rho U C K x).length := by
  rw [nuclei_length]
  positivity

theorem nuclei_values_nodup (rho U C K : ℕ) (x : Input) (hN : 0 < x.1.1.2)
    (G : Position → Position) {J : ℝ≥0} (hG : AntilipschitzWith J G)
    (herror : ∀ l : TransformedGauss.Label,
      ‖CappedKernelProgram.position (TransformedGauss.value rho U C K x.1.1.1 x.1.1.2
          x.1.2.1.1 x.1.2.1.2 x.1.2.2 l.1 l.2)-
        G (gaussLatticePoint (x.1.1.2:ℝ)⁻¹ (RationalGaussNodes.index l.1 l.2))‖ ≤
          ((x.1.1.1:ℝ)+1)⁻¹)
    (hprecision : 2*(J:ℝ)*((x.1.1.1:ℝ)+1)⁻¹ < (x.1.1.2:ℝ)⁻¹/3) :
    ((nuclei rho U C K x).map BinaryPosition.value).Nodup := by
  have hn := TransformedGauss.nodes_nodup rho U C K x.1.1.1 hN x.1.2.1.1 x.1.2.1.2
    x.1.2.2 (CenteredGaussLabels.labels x.2) (CenteredGaussLabels.labels_nodup x.2)
    G hG herror hprecision
  have hm := hn.map NuclearCoordinateOutput.position_value_injective
  simpa only [nuclei,NuclearCoordinateOutput.positions,List.map_map,Function.comp_def] using hm

end ContinuumCoulomb.CenteredNuclearProgram

end OAI
