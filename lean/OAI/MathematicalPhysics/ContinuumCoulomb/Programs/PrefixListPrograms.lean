import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PrefixPrograms
import OAI.Computability.QuantumFactoring.BitStackListWords
import OAI.Computability.QuantumFactoring.NativeAIGAddWrapper

namespace OAI

/-! Actual conversion of the source's counted prefix list to quoted
machine list registers. Each field is parsed by its literal splitter;
the loop count and all temporary word lengths are bounded by the input. -/

namespace ContinuumCoulomb.PrefixListPrograms
open ExactQuantumFactoring.BitStackProgram PrefixPrograms

abbrev State (α : Type) := List α × (List Bool × List α)

def stateView {α : Type} (c : BinaryEncoding.Codec α) (s : State α) :
    ℕ × (List Bool × List α) := (s.1.length, (s.1.flatMap c.encode ++ s.2.1, s.2.2))

def stateCode {α : Type} (c : BinaryEncoding.Codec α) : State α → List Bool :=
  fun s => prodCode Nat.bits (prodCode id (listCode c.encode)) (stateView c s)

def step {α : Type} (s : State α) : State α :=
  match s.1 with
  | [] => s
  | a :: xs => (xs, s.2.1, a :: s.2.2)

theorem step_iterate {α : Type} (i : ℕ) (xs : List α) (tail : List Bool) (acc : List α) :
    step^[i] (xs, tail, acc) = (xs.drop i, tail, (xs.take i).reverse ++ acc) := by
  induction i generalizing xs acc with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil => simpa [step] using ih [] acc
    | cons a xs => simpa [step, List.reverse_cons, List.append_assoc] using ih xs (a :: acc)

theorem flat_length {α : Type} (c : BinaryEncoding.Codec α) (hc : ∀ a, 0 < (c.encode a).length)
    (xs : List α) : xs.length ≤ (xs.flatMap c.encode).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hc a
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

theorem quoted_length {α : Type} (c : BinaryEncoding.Codec α) (xs : List α) :
    (listCode c.encode xs).length = 2 * (xs.flatMap c.encode).length + 2 * xs.length + 1 := by
  induction xs with
  | nil => simp [listCode]
  | cons a xs ih =>
    simp only [listCode_length_cons, List.flatMap_cons, List.length_append, List.length_cons, ih]
    omega

theorem stateCode_length {α : Type} (c : BinaryEncoding.Codec α) (s : State α) :
    (stateCode c s).length = 2 * s.1.length.bits.length +
      2 * ((s.1.flatMap c.encode).length + s.2.1.length) + 2 + (listCode c.encode s.2.2).length := by
  simp only [stateCode, stateView, prodCode, pairBits_length, List.length_append, id_eq]
  omega

theorem state_growth {α : Type} (c : BinaryEncoding.Codec α)
    (hc : ∀ a, 0 < (c.encode a).length) (s : State α) (i : ℕ) :
    (stateCode c (step^[i] s)).length ≤ 3 * (stateCode c s).length + 1 := by
  rcases s with ⟨xs, tail, acc⟩
  rw [step_iterate]
  have hn := bits_length_mono (show (xs.drop i).length ≤ xs.length by simp only [List.length_drop]; omega)
  have hsplit : ((xs.take i).flatMap c.encode).length + ((xs.drop i).flatMap c.encode).length =
      (xs.flatMap c.encode).length := by
    rw [← List.length_append, ← List.flatMap_append, List.take_append_drop]
  have hl := flat_length c hc xs
  have hacc := listCode_length_append c.encode (xs.take i).reverse acc
  rw [listCode_length_rev] at hacc
  have htake := listCode_length_take_le c.encode i xs
  rw [quoted_length c xs] at htake
  simp only [stateCode_length]
  omega

noncomputable def listOutput {α : Type} (c : BinaryEncoding.Codec α) (d : α) :
    Procedure (listCode c.encode) (BinaryEncoding.list c).encode id := by
  let emit : Procedure c.encode id c.encode := (Procedure.identity c.encode).result (by intro a; rfl)
  let flat := Procedure.listFlatMapWords d emit
  let count := Procedure.unaryToBits.comp (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength c.encode d)
  let header : Procedure (listCode c.encode) id (fun xs => BinaryEncoding.natural.encode xs.length) :=
    (EncodingPrograms.naturalOutput.comp count).result (by intro xs; rfl)
  exact (Procedure.append.comp (header.pair flat)).result (by intro xs; rfl)

section Parser
variable {α : Type} (c : BinaryEncoding.Codec α) (pc : Splitter c) (d : α)

noncomputable def countProgram : Procedure (stateCode c) Nat.bits (fun s => s.1.length) :=
  (Procedure.first Nat.bits (prodCode id (listCode c.encode))).precompose (stateView c)

noncomputable def streamProgram : Procedure (stateCode c) id
    (fun s => s.1.flatMap c.encode ++ s.2.1) :=
  ((Procedure.first id (listCode c.encode)).comp
    (Procedure.second Nat.bits (prodCode id (listCode c.encode)))).precompose (stateView c)

noncomputable def accProgram : Procedure (stateCode c) (listCode c.encode) (fun s => s.2.2) :=
  ((Procedure.second id (listCode c.encode)).comp
    (Procedure.second Nat.bits (prodCode id (listCode c.encode)))).precompose (stateView c)

abbrev NonemptyState (α : Type) := {s : State α // ¬s.1 = []}

noncomputable def headerProgram : Procedure (fun s : NonemptyState α => stateCode c s.val)
    (prodCode c.encode id)
    (fun s => (s.val.1.headD d, s.val.1.tail.flatMap c.encode ++ s.val.2.1)) := by
  let word := (streamProgram c).precompose (fun s : NonemptyState α => s.val)
  let asPrefix : Procedure (fun s : NonemptyState α => stateCode c s.val) (prefixCode c)
      (fun s => (s.val.1.headD d, s.val.1.tail.flatMap c.encode ++ s.val.2.1)) :=
    word.result (by
      rintro ⟨⟨xs, tail, acc⟩, h⟩
      cases xs with
      | nil => contradiction
      | cons a xs => simp only [List.flatMap_cons, List.headD_cons, List.tail_cons, prefixCode,
          id_eq, List.append_assoc])
  exact pc.comp asPrefix

noncomputable def nonemptyStep : Procedure (fun s : NonemptyState α => stateCode c s.val)
    (stateCode c) (fun s => step s.val) := by
  let head : Procedure (fun s : NonemptyState α => stateCode c s.val) c.encode
      (fun s => s.val.1.headD d) :=
    (Procedure.first c.encode id).comp (headerProgram c pc d)
  let tail : Procedure (fun s : NonemptyState α => stateCode c s.val) id
      (fun s => s.val.1.tail.flatMap c.encode ++ s.val.2.1) :=
    (Procedure.second c.encode id).comp (headerProgram c pc d)
  let acc := (accProgram c).precompose (fun s : NonemptyState α => s.val)
  let nextAcc := (Procedure.listCons c.encode).comp (head.pair acc)
  let count := (countProgram c).precompose (fun s : NonemptyState α => s.val)
  let nextCount := Procedure.binarySub.comp (count.pair
    (Procedure.constant (fun s : NonemptyState α => stateCode c s.val) Nat.bits 1))
  exact (nextCount.pair (tail.pair nextAcc)).result (by
    rintro ⟨⟨xs, tail, acc⟩, h⟩
    cases xs with
    | nil => contradiction
    | cons a xs => simp only [stateCode, stateView, step, List.headD_cons, List.tail_cons,
        List.length_cons, Nat.add_sub_cancel, Function.comp_apply])

noncomputable def stepProgram : Procedure (stateCode c) (stateCode c) step := by
  let test : Procedure (stateCode c) Procedure.boolCode (fun s => decide (s.1 = [])) :=
    (Procedure.binaryZero.comp (countProgram c)).congrFun (by
      intro s
      simp only [Function.comp_apply, List.length_eq_zero_iff])
  let yes : Procedure (fun s : {s : State α // s.1 = []} => stateCode c s.val)
      (stateCode c) (fun s => step s.val) :=
    ((Procedure.identity (stateCode c)).precompose (fun s : {s : State α // s.1 = []} => s.val)).congrFun
      (by intro s; simp only [id_eq, step, s.property])
  exact Procedure.splitOn (fun s : State α => s.1 = []) test yes (nonemptyStep c pc d)

noncomputable def iterationProgram (hc : ∀ a, 0 < (c.encode a).length) :
    Procedure (prodCode unaryCode (stateCode c)) (stateCode c) (fun x => step^[x.1] x.2) :=
  (stepProgram c pc d).iterate (Polynomial.C 3 * Polynomial.X + 1) (by
    intro n s i _
    have h := state_growth c hc s i
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_one]
    omega)

noncomputable def inputCount : Procedure (prefixCode (BinaryEncoding.list c)) Nat.bits
    (fun x => x.1.length) :=
  ((Procedure.first Nat.bits id).precompose
    (fun x : List α × List Bool => (x.1.length, x.1.flatMap c.encode ++ x.2))).congrEncoding (by
      intro x
      change quoteBits x.1.length.bits ++ (x.1.flatMap c.encode ++ x.2) =
        (BinaryEncoding.encodeDigits x.1.length.bits ++ x.1.flatMap c.encode) ++ x.2
      rw [AmplificationProgram.encodeDigits_quote, List.append_assoc]) (by intro x; rfl)

noncomputable def inputStream : Procedure (prefixCode (BinaryEncoding.list c)) id
    (fun x => x.1.flatMap c.encode ++ x.2) :=
  ((Procedure.second Nat.bits id).precompose
    (fun x : List α × List Bool => (x.1.length, x.1.flatMap c.encode ++ x.2))).congrEncoding (by
      intro x
      change quoteBits x.1.length.bits ++ (x.1.flatMap c.encode ++ x.2) =
        (BinaryEncoding.encodeDigits x.1.length.bits ++ x.1.flatMap c.encode) ++ x.2
      rw [AmplificationProgram.encodeDigits_quote, List.append_assoc]) (by intro x; rfl)

noncomputable def startProgram : Procedure (prefixCode (BinaryEncoding.list c)) (stateCode c)
    (fun x => (x.1, x.2, [])) :=
  ((inputCount c).pair ((inputStream c).pair
    (Procedure.constant (prefixCode (BinaryEncoding.list c)) (listCode c.encode) []))).result
      (by intro x; rfl)

theorem input_length (hc : ∀ a, 0 < (c.encode a).length) (x : List α × List Bool) :
    x.1.length ≤ (prefixCode (BinaryEncoding.list c) x).length := by
  have h := flat_length c hc x.1
  change x.1.length ≤ ((BinaryEncoding.natural.encode x.1.length ++ x.1.flatMap c.encode) ++ x.2).length
  simp only [List.length_append]
  omega

noncomputable def parseProgram (hc : ∀ a, 0 < (c.encode a).length) :
    Procedure (prefixCode (BinaryEncoding.list c)) (stateCode c)
      (fun x => ([], x.2, x.1.reverse)) := by
  let times : Procedure (prefixCode (BinaryEncoding.list c)) unaryCode
      (fun x => (prefixCode (BinaryEncoding.list c) x).length) :=
    Procedure.length.precompose (prefixCode (BinaryEncoding.list c))
  exact ((iterationProgram c pc d hc).comp (times.pair (startProgram c))).congrFun (by
    intro x
    change step^[(prefixCode (BinaryEncoding.list c) x).length] (x.1, x.2, []) = _
    rw [step_iterate, List.drop_eq_nil_of_le (input_length c hc x),
      List.take_of_length_le (input_length c hc x), List.append_nil])

noncomputable def parsedList (hc : ∀ a, 0 < (c.encode a).length) :
    Procedure (prefixCode (BinaryEncoding.list c)) (listCode c.encode) Prod.fst :=
  ((Procedure.listReverse c.encode d).comp ((accProgram c).comp (parseProgram c pc d hc))).congrFun
    (by intro x; exact List.reverse_reverse x.1)

noncomputable def parsedTail (hc : ∀ a, 0 < (c.encode a).length) :
    Procedure (prefixCode (BinaryEncoding.list c)) id Prod.snd :=
  ((streamProgram c).comp (parseProgram c pc d hc)).congrFun (by intro x; rfl)

noncomputable def listSplitter (hc : ∀ a, 0 < (c.encode a).length) : Splitter (BinaryEncoding.list c) :=
  (((listOutput c d).comp (parsedList c pc d hc)).pair (parsedTail c pc d hc)).congrFun (by intro x; rfl)

/-- Actual quoted-list conversion for a complete source field, with no
postulated record-decoding primitive. -/
noncomputable def listInput (hc : ∀ a, 0 < (c.encode a).length) :
    Procedure (BinaryEncoding.list c).encode (listCode c.encode) id :=
  ((parsedList c pc d hc).precompose (fun xs : List α => (xs, []))).congrEncoding
    (by intro xs; exact List.append_nil _) (by intro xs; rfl)

end Parser

end ContinuumCoulomb.PrefixListPrograms

end OAI
