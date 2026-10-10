import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.AmplificationProgram
import OAI.Computability.QuantumFactoring.BitStackIntegers

namespace OAI

/-! Actual finite-stack parsing and serialization routines for the coordinate codes. Sign bits, natural-number marker bits, and field tails
are read by the program rather than by an assumed record-decoding operation. -/

namespace ContinuumCoulomb.BinaryEncoding

/-- Quote a prefix code so an existing word-stack product parser can read
the field. The quoting overhead is exactly linear. -/
def quoted {α : Type} (c : Codec α) : Codec α where
  encode x := encodeDigits (c.encode x)
  read s := let (xs, tail) := readDigits s; ((c.read xs).1, tail)
  read_encode x tail := by
    simp only [readDigits_encode]
    have h := congrArg Prod.fst (c.read_encode x [])
    simpa only [List.append_nil, Prod.fst] using congrArg (fun a => (a, tail)) h

theorem quoted_length {α : Type} (c : Codec α) (x : α) :
    ((quoted c).encode x).length = 2 * (c.encode x).length + 1 :=
  encodeDigits_length _

end ContinuumCoulomb.BinaryEncoding

namespace ContinuumCoulomb.EncodingPrograms
open ExactQuantumFactoring.BitStackProgram

def integerPayload : ℤ → ℕ
  | .ofNat n => n
  | .negSucc n => n

def integerNegative : ℤ → Bool
  | .ofNat _ => false
  | .negSucc _ => true

noncomputable def naturalInput : Procedure BinaryEncoding.natural.encode Nat.bits id := by
  let p := (Procedure.first Nat.bits (fun _ : Unit => [])).precompose (fun n : ℕ => (n, ()))
  exact p.congrEncoding (by
    intro n
    change quoteBits n.bits ++ [] = BinaryEncoding.encodeDigits n.bits
    rw [List.append_nil, AmplificationProgram.encodeDigits_quote]) (by intro n; rfl)

noncomputable def naturalOutput : Procedure Nat.bits BinaryEncoding.natural.encode id :=
  (Procedure.quote Nat.bits).result
    (by intro n; exact (AmplificationProgram.encodeDigits_quote n.bits).symm)

theorem quotedPair_encoding {α β : Type} (c : BinaryEncoding.Codec α)
    (d : BinaryEncoding.Codec β) (x : α × β) :
    (BinaryEncoding.pair (BinaryEncoding.quoted c) d).encode x = prodCode c.encode d.encode x := by
  change BinaryEncoding.encodeDigits (c.encode x.1) ++ _ = quoteBits (c.encode x.1) ++ _
  rw [AmplificationProgram.encodeDigits_quote]

noncomputable def quotedFirst {α β : Type} (c : BinaryEncoding.Codec α)
    (d : BinaryEncoding.Codec β) :
    Procedure (BinaryEncoding.pair (BinaryEncoding.quoted c) d).encode c.encode Prod.fst :=
  (Procedure.first c.encode d.encode).congrEncoding
    (fun x => (quotedPair_encoding c d x).symm) (by intro x; rfl)

noncomputable def quotedSecond {α β : Type} (c : BinaryEncoding.Codec α)
    (d : BinaryEncoding.Codec β) :
    Procedure (BinaryEncoding.pair (BinaryEncoding.quoted c) d).encode d.encode Prod.snd :=
  (Procedure.second c.encode d.encode).congrEncoding
    (fun x => (quotedPair_encoding c d x).symm) (by intro x; rfl)

/-- Serialize two already encoded fields by actual word concatenation. -/
noncomputable def appendPair {α β : Type} (c : BinaryEncoding.Codec α)
    (d : BinaryEncoding.Codec β) :
    Procedure (prodCode c.encode d.encode) (BinaryEncoding.pair c d).encode id :=
  (Procedure.append.precompose (fun x : α × β => (c.encode x.1, d.encode x.2))).result
    (by intro x; rfl)

theorem naturalPair_encoding {α : Type} (c : BinaryEncoding.Codec α) (x : ℕ × α) :
    prodCode Nat.bits c.encode x = (BinaryEncoding.pair BinaryEncoding.natural c).encode x := by
  change quoteBits x.1.bits ++ _ = BinaryEncoding.encodeDigits x.1.bits ++ _
  rw [AmplificationProgram.encodeDigits_quote]

noncomputable def naturalFirst {α : Type} (c : BinaryEncoding.Codec α) :
    Procedure (BinaryEncoding.pair BinaryEncoding.natural c).encode Nat.bits Prod.fst :=
  (Procedure.first Nat.bits c.encode).congrEncoding (naturalPair_encoding c) (by intro n; rfl)

noncomputable def naturalSecond {α : Type} (c : BinaryEncoding.Codec α) :
    Procedure (BinaryEncoding.pair BinaryEncoding.natural c).encode c.encode Prod.snd :=
  (Procedure.second Nat.bits c.encode).congrEncoding (naturalPair_encoding c) (by intro n; rfl)

/-- Read and remove the actual sign bit, retaining the coordinate payload
and the entire following encoded field. -/
noncomputable def integerPairPayload {α : Type} (c : BinaryEncoding.Codec α) :
    Procedure (BinaryEncoding.pair BinaryEncoding.integer c).encode
      (prodCode Nat.bits c.encode) (fun x => (integerPayload x.1, x.2)) :=
  (Procedure.tail.precompose (BinaryEncoding.pair BinaryEncoding.integer c).encode).result (by
    rintro ⟨z, y⟩
    cases z with
    | ofNat n =>
      change BinaryEncoding.encodeDigits n.bits ++ c.encode y = quoteBits n.bits ++ c.encode y
      rw [AmplificationProgram.encodeDigits_quote]
    | negSucc n =>
      change BinaryEncoding.encodeDigits n.bits ++ c.encode y = quoteBits n.bits ++ c.encode y
      rw [AmplificationProgram.encodeDigits_quote])

noncomputable def integerPairSign {α : Type} (c : BinaryEncoding.Codec α) :
    Procedure (BinaryEncoding.pair BinaryEncoding.integer c).encode Procedure.boolCode
      (fun x => integerNegative x.1) :=
  (Procedure.head.precompose (BinaryEncoding.pair BinaryEncoding.integer c).encode).congrFun (by
    rintro ⟨z, y⟩
    cases z <;> rfl)

noncomputable def integerFirst {α : Type} (c : BinaryEncoding.Codec α) :
    Procedure (BinaryEncoding.pair BinaryEncoding.integer c).encode intCode Prod.fst := by
  let payload := (Procedure.first Nat.bits c.encode).comp (integerPairPayload c)
  let positive := Procedure.natToInt.comp payload
  let negative := Procedure.intNeg.comp (Procedure.natToInt.comp
    (Procedure.successor.comp payload))
  exact (Procedure.conditional (integerPairSign c) negative positive).congrFun (by
    rintro ⟨z, y⟩
    cases z with
    | ofNat n => rfl
    | negSucc n =>
      change -(↑(n + 1) : ℤ) = Int.negSucc n
      omega)

noncomputable def integerSecond {α : Type} (c : BinaryEncoding.Codec α) :
    Procedure (BinaryEncoding.pair BinaryEncoding.integer c).encode c.encode Prod.snd :=
  ((Procedure.second Nat.bits c.encode).comp (integerPairPayload c)).congrFun (by intro x; rfl)

def emptyUnit : BinaryEncoding.Codec Unit where
  encode _ := []
  read s := ((), s)
  read_encode x tail := by cases x; rfl

noncomputable def integerInput : Procedure BinaryEncoding.integer.encode intCode id :=
  ((integerFirst emptyUnit).precompose (fun z => (z, ()))).congrEncoding
    (by intro z; exact List.append_nil _) (by intro z; rfl)

/-- Convert signed-magnitude stack integers to the exact signed-coordinate convention
whose negative payload is one less than its absolute value. -/
noncomputable def integerOutput : Procedure intCode BinaryEncoding.integer.encode id := by
  let positivePrefix : Procedure Nat.bits BinaryEncoding.integer.encode (fun n => (n : ℤ)) :=
    ((Procedure.prepend BinaryEncoding.natural.encode [false]).comp naturalOutput).result
      (by intro n; rfl)
  let negativePrefix : Procedure Nat.bits BinaryEncoding.integer.encode
      (fun n => Int.negSucc n) :=
    ((Procedure.prepend BinaryEncoding.natural.encode [true]).comp naturalOutput).result
      (by intro n; rfl)
  let magnitudePred := Procedure.binarySub.comp
    (Procedure.intAbs.pair (Procedure.constant intCode Nat.bits 1))
  exact (Procedure.conditional Procedure.intSign
    (negativePrefix.comp magnitudePred) (positivePrefix.comp Procedure.intAbs)).congrFun (by
      intro z
      cases z <;> simp)

/-- Scaling and translating a signed lattice coordinate uses genuine binary
arithmetic and emits the signed-coordinate code. -/
noncomputable def affineCoordinate (scale offset : ℤ) :
    Procedure BinaryEncoding.integer.encode BinaryEncoding.integer.encode
      (fun z => scale * z + offset) := by
  let product := Procedure.intMul.comp
    ((Procedure.constant BinaryEncoding.integer.encode intCode scale).pair integerInput)
  let sum := Procedure.intAdd.comp
    (product.pair (Procedure.constant BinaryEncoding.integer.encode intCode offset))
  exact (integerOutput.comp sum).congrFun (by intro z; rfl)

noncomputable def affineCoordinate_certificate (scale offset : ℤ) :
    Turing.TM2ComputableInPolyTime BinaryEncoding.integer.encode BinaryEncoding.integer.encode
      (fun z => scale * z + offset) := (affineCoordinate scale offset).toTM2

end ContinuumCoulomb.EncodingPrograms

end OAI
