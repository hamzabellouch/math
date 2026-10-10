import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PhysicalNuclearProgram

namespace OAI

/-! The literal output codec for a complete unit-charge Coulomb instance.
The electron count is unary, and both rational thresholds are emitted in
canonical numerator/positive-denominator form. -/

namespace ContinuumCoulomb.UnitCoulombProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := PhysicalNuclearProgram.Input×(ℕ×(ℚ×ℚ))
def metadataCode : (ℕ×(ℚ×ℚ)) → List Bool := prodCode unaryCode (prodCode ratCode ratCode)
def inputCode : Input → List Bool := prodCode PhysicalNuclearProgram.inputCode metadataCode

noncomputable def value (rho U C K : ℕ) (x : Input) : UnitCoulomb where
  nuclei := PhysicalNuclearProgram.nuclei rho U C K x.1
  electrons := x.2.1
  lower := NuclearCoordinateOutput.rational x.2.2.1
  upper := NuclearCoordinateOutput.rational x.2.2.2

noncomputable opaque unaryOutput : Procedure unaryCode BinaryEncoding.unary.encode id := by
  let bytes : Procedure unaryCode (id : List Bool → List Bool) unaryCode :=
    (Procedure.identity unaryCode).result (by intro n; rfl)
  let p := Procedure.append.comp
    (bytes.pair (Procedure.constant unaryCode (id : List Bool → List Bool) [false]))
  exact p.result (by intro n; exact (AmplificationProgram.encodeUnary_replicate n).symm)

noncomputable opaque geometryProgram : Procedure inputCode PhysicalNuclearProgram.inputCode Prod.fst :=
  Procedure.first _ _
noncomputable opaque metadataProgram : Procedure inputCode metadataCode Prod.snd := Procedure.second _ _
noncomputable opaque electronsProgram : Procedure inputCode BinaryEncoding.unary.encode (fun x => x.2.1) :=
  unaryOutput.comp ((Procedure.first _ _).comp metadataProgram)
noncomputable opaque thresholdsInputProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.2.2) := (Procedure.second _ _).comp metadataProgram

noncomputable opaque thresholdsProgram : Procedure inputCode SourcePrograms.thresholdCodec.encode
    (fun x => (NuclearCoordinateOutput.rational x.2.2.1,NuclearCoordinateOutput.rational x.2.2.2)) :=
  (EncodingPrograms.appendPair binaryRationalCodec binaryRationalCodec).comp
    ((NuclearCoordinateOutput.rationalProgram.comp ((Procedure.first _ _).comp thresholdsInputProgram)).pair
      (NuclearCoordinateOutput.rationalProgram.comp ((Procedure.second _ _).comp thresholdsInputProgram)))

noncomputable opaque tailProgram : Procedure inputCode UnitBinaryProgram.tailCodec.encode
    (fun x => (x.2.1,(NuclearCoordinateOutput.rational x.2.2.1,NuclearCoordinateOutput.rational x.2.2.2))) :=
  (EncodingPrograms.appendPair BinaryEncoding.unary SourcePrograms.thresholdCodec).comp
    (electronsProgram.pair thresholdsProgram)

noncomputable opaque program (rho U C K : ℕ) : Procedure inputCode unitCoulombCodec.encode (value rho U C K) :=
  ((EncodingPrograms.appendPair (BinaryEncoding.list binaryPositionCodec) UnitBinaryProgram.tailCodec).comp
    (((PhysicalNuclearProgram.program rho U C K).comp geometryProgram).pair tailProgram)).result
      (by intro x; rfl)

noncomputable def certificate (rho U C K : ℕ) : Turing.TM2ComputableInPolyTime inputCode
    unitCoulombCodec.encode (value rho U C K) := (program rho U C K).toTM2

private theorem positions_injective {ns : List BinaryPosition}
    (h : (ns.map BinaryPosition.value).Nodup) :
    Function.Injective (fun a : Fin ns.length => (ns.get a).value) := by
  intro i j hij
  apply Fin.ext
  apply h.eq_of_getElem_eq (by simp) (by simp)
  simpa only [List.getElem_map,List.get_eq_getElem] using hij

theorem valid (rho U C K : ℕ) (x : Input) (helectrons : 0 < x.2.1)
    (hpositions : ((PhysicalNuclearProgram.nuclei rho U C K x.1).map BinaryPosition.value).Nodup)
    (hgap : (1:ℚ) ≤ x.2.2.2-x.2.2.1) : (value rho U C K x).Valid where
  nuclei_pos := PhysicalNuclearProgram.nuclei_nonempty rho U C K x.1
  electrons_pos := helectrons
  positions a := PhysicalNuclearProgram.nuclei_valid rho U C K x.1 (List.get_mem _ a)
  distinct := positions_injective hpositions
  lower_denominator := x.2.2.1.den_pos
  upper_denominator := x.2.2.2.den_pos
  gap := by simpa only [value,NuclearCoordinateOutput.rational_value] using hgap

theorem valid_of_nodes (rho U C K : ℕ) (x : Input) (hrho : 0 < rho)
    (hN : 0 < x.1.1.1.2) (helectrons : 0 < x.2.1)
    (hnodes : (TransformedGauss.nodes rho U C K
      (x.1.1,CenteredGaussLabels.labels x.1.2)).Nodup)
    (hgap : (1:ℚ) ≤ x.2.2.2-x.2.2.1) : (value rho U C K x).Valid :=
  valid rho U C K x helectrons
    (PhysicalNuclearProgram.nuclei_values_nodup rho U C K x.1 hrho hN hnodes) hgap

end ContinuumCoulomb.UnitCoulombProgram

end OAI
