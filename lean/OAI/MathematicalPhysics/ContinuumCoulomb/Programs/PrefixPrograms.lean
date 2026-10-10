import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorProgram
import OAI.Computability.QuantumFactoring.BitStackDependentChoice
import OAI.Computability.QuantumFactoring.BitStackBoundedUnary
import OAI.Computability.QuantumFactoring.BitStackListOps

namespace OAI

/-! Literal prefixCode parsing for the source serialization. A parser emits
the first encoded field and its untouched following bit string. -/

namespace ContinuumCoulomb.PrefixPrograms
open ExactQuantumFactoring.BitStackProgram

def prefixCode {α : Type} (c : BinaryEncoding.Codec α) (x : α × List Bool) : List Bool :=
  c.encode x.1 ++ x.2

abbrev Splitter {α : Type} (c : BinaryEncoding.Codec α) :=
  Procedure (prefixCode c) (prodCode c.encode id) id

noncomputable def natural : Splitter BinaryEncoding.natural := by
  let num : Procedure (prodCode Nat.bits id) BinaryEncoding.natural.encode Prod.fst :=
    EncodingPrograms.naturalOutput.comp (Procedure.first Nat.bits id)
  let tail : Procedure (prodCode Nat.bits id) id Prod.snd := Procedure.second Nat.bits id
  exact (num.pair tail).congrEncoding (by
    intro x
    change quoteBits x.1.bits ++ x.2 = BinaryEncoding.encodeDigits x.1.bits ++ x.2
    rw [AmplificationProgram.encodeDigits_quote]) (by intro x; rfl)

noncomputable def integerPayload : Procedure (prefixCode BinaryEncoding.integer)
    (prodCode Nat.bits id) (fun x => (EncodingPrograms.integerPayload x.1, x.2)) :=
  (Procedure.tail.precompose (prefixCode BinaryEncoding.integer)).result (by
    rintro ⟨z, s⟩
    cases z <;>
      change BinaryEncoding.encodeDigits _ ++ s = quoteBits _ ++ s <;>
      rw [AmplificationProgram.encodeDigits_quote] <;> rfl)

noncomputable def integerSign : Procedure (prefixCode BinaryEncoding.integer) Procedure.boolCode
    (fun x => EncodingPrograms.integerNegative x.1) :=
  (Procedure.head.precompose (prefixCode BinaryEncoding.integer)).congrFun (by
    rintro ⟨z, s⟩
    cases z <;> rfl)

noncomputable def integerValue : Procedure (prefixCode BinaryEncoding.integer) intCode Prod.fst := by
  let payload : Procedure (prefixCode BinaryEncoding.integer) Nat.bits
      (fun x => EncodingPrograms.integerPayload x.1) :=
    (Procedure.first Nat.bits id).comp integerPayload
  let positive := Procedure.natToInt.comp payload
  let negative := Procedure.intNeg.comp (Procedure.natToInt.comp (Procedure.successor.comp payload))
  exact (Procedure.conditional integerSign negative positive).congrFun (by
    rintro ⟨z, s⟩
    cases z with
    | ofNat n => rfl
    | negSucc n => change -(↑(n + 1) : ℤ) = Int.negSucc n; omega)

noncomputable def integer : Splitter BinaryEncoding.integer :=
  ((EncodingPrograms.integerOutput.comp integerValue).pair
    ((Procedure.second Nat.bits id).comp integerPayload)).congrFun (by intro x; rfl)

section Pair
variable {α β : Type} (c : BinaryEncoding.Codec α) (d : BinaryEncoding.Codec β)
variable (pc : Splitter c) (pd : Splitter d)

noncomputable def pairHeader : Procedure (prefixCode (BinaryEncoding.pair c d))
    (prodCode c.encode (prefixCode d)) (fun x => (x.1.1, (x.1.2, x.2))) :=
  ((pc.precompose (fun x : (α × β) × List Bool => (x.1.1, d.encode x.1.2 ++ x.2))).congrEncoding
    (by intro x; exact (List.append_assoc _ _ _).symm) (by intro x; rfl)).result
      (by intro x; rfl)

noncomputable def pairFirst : Procedure (prefixCode (BinaryEncoding.pair c d)) c.encode
    (fun x => x.1.1) := (Procedure.first c.encode (prefixCode d)).comp (pairHeader c d pc)

noncomputable def pairRest : Procedure (prefixCode (BinaryEncoding.pair c d)) (prodCode d.encode id)
    (fun x => (x.1.2, x.2)) :=
  pd.comp ((Procedure.second c.encode (prefixCode d)).comp (pairHeader c d pc))

noncomputable def pairSecond : Procedure (prefixCode (BinaryEncoding.pair c d)) d.encode
    (fun x => x.1.2) := (Procedure.first d.encode id).comp (pairRest c d pc pd)

noncomputable def pairTail : Procedure (prefixCode (BinaryEncoding.pair c d)) id
    (fun x => x.2) := (Procedure.second d.encode id).comp (pairRest c d pc pd)

noncomputable def pairValue : Procedure (prefixCode (BinaryEncoding.pair c d))
    (BinaryEncoding.pair c d).encode (fun x => x.1) :=
  ((EncodingPrograms.appendPair c d).comp
    ((pairFirst c d pc).pair (pairSecond c d pc pd))).congrFun (by intro x; rfl)

noncomputable def pair : Splitter (BinaryEncoding.pair c d) :=
  ((pairValue c d pc pd).pair (pairTail c d pc pd)).congrFun (by intro x; rfl)

end Pair

noncomputable def rational : Splitter MediatorProgram.rationalCodec := by
  let p := pair BinaryEncoding.integer BinaryEncoding.natural integer natural
  exact (p.precompose (fun x : ℚ × List Bool => ((x.1.num, x.1.den), x.2))).result
    (by intro x; rfl)

end ContinuumCoulomb.PrefixPrograms

end OAI
