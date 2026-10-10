import OAI.Computability.UniqueGames.Decoding.TableKeysAddressGameLemmas
import OAI.Computability.UniqueGames.Machines.GraphCounterStartLemmas
import OAI.Computability.UniqueGames.Machines.MachineSingleOrbitFinishLemmas
import OAI.Computability.UniqueGames.Reduction.AddressMachineLoopLemmas

namespace OAI

section

/-!
The old addressed producer is reused only as a code generator. Its exact output
is the doubled codec of the new single-orbit game. The proved physical
postprocessor then yields the new game, with no premise about the value of the
legacy game and no legacy gadget or inverse theorem used.
-/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge

open Turing UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Complexity
open ActualSource MachineSingleOrbitCodec

namespace SingleAddress

abbrev vertexCount := Decoder.TableKeysAddressGame.vertexCount
abbrev queryAddress := Decoder.TableKeysAddressGame.queryAddress
abbrev addressEdge := Decoder.TableKeysAddressGame.addressEdge
abbrev outputInstance := Decoder.TableKeysAddressGame.outputInstance
abbrev tableOutput := Decoder.TableKeysAddressGame.tableOutput

end SingleAddress

theorem old_addressEdge_eq_double (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    AddressGame.addressEdge S k g ω = doubleConstraint (SingleAddress.addressEdge S k g ω) := by
  unfold AddressGame.addressEdge doubleConstraint SingleAddress.addressEdge
    Decoder.TableKeysAddressGame.addressEdge
  congr 1
  apply Fin.ext
  exact Encoding.sideEquiv_true_val _

/-- Exact equality of the ordered, fully serialized constraint data. -/
theorem old_outputInstance_eq_double (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    AddressGame.outputInstance S k g en = doubleInstance (SingleAddress.outputInstance S k g en) := by
  unfold AddressGame.outputInstance doubleInstance SingleAddress.outputInstance
    Decoder.TableKeysAddressGame.outputInstance
  congr 1
  simp only [List.map_map, Function.comp_def, ← old_addressEdge_eq_double]
  rfl

theorem old_tableOutput_eq_double (S : Source) (k : Nat) {s d : Nat}
    (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d) :
    AddressGame.tableOutput S k T = doubleInstance (SingleAddress.tableOutput S k T) :=
  old_outputInstance_eq_double S k _ _

def output (k : Nat) {s d : Nat} (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d)
    (input : SourceEncoding.Input) : UniqueGamesTheorem.Foundations.Target.Instance (2 ^ s) :=
  SingleAddress.tableOutput (Source.ofList input.equations input.nonempty) k T

theorem old_output_eq_double (k : Nat) {s d : Nat}
    (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d) (input : SourceEncoding.Input) :
    MachineAddressGame.output k T input = doubleInstance (output k T input) :=
  old_tableOutput_eq_double _ k T

noncomputable section

/-- Reinterpret the existing producer using the proved exact codec equality. -/
def doubledComputableInPolyTime (k : Nat) {s d : Nat}
    (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d) :
    TM2ComputableInPolyTime SourceEncoding.inputBits
      (fun I => gameBits (doubleInstance I)) (output k T) := by
  let old := MachineAddressGame.computableInPolyTime k T
  refine {
    tm := old.tm
    inputAlphabet := old.inputAlphabet
    outputAlphabet := old.outputAlphabet
    time := old.time
    outputsFun := ?_ }
  intro input
  rw [← old_output_eq_double k T input]
  exact old.outputsFun input

def computableInPolyTime (k : Nat) {s d : Nat}
    (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d) :
    TM2ComputableInPolyTime SourceEncoding.inputBits gameBits (output k T) :=
  MachineSequential.composeBits (f := output k T) (g := id) (doubledComputableInPolyTime k T)
    (MachineSingleOrbitRuntime.computableInPolyTime (2 ^ s))

end

end UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge

end

section

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge

theorem workAlphabetFinite (k : Nat) {s d : Nat}
    (T : UniqueGamesTheorem.Integration.NoiseTables.Table s d)
    (tape : (computableInPolyTime k T).tm.K) :
    Finite ((computableInPolyTime k T).tm.Γ tape) := by
  rcases tape with first | second
  · change Finite Bool
    infer_instance
  · rcases second with localTape | bridgeTape
    · change Finite Bool
      infer_instance
    · change Finite Bool
      infer_instance

end UniqueGamesTheorem.Explicit.MachineSingleOrbitBridge

end

end OAI
