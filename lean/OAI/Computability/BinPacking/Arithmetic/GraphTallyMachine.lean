import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Induction
import OAI.Computability.BinPacking.Computation.MachineHorner
import OAI.Computability.BinPacking.Packing.FractionWidth
import OAI.Computability.BinPacking.Packing.K4Graph
import OAI.Computability.BinPacking.Reductions.BinaryTokenMachine

namespace OAI

namespace BinPackingGap.BinaryEncoding

def parseOption {α : Type} (parse : Parser α) : Parser (Option α)
  | [] => none
  | false :: rest => some (none, rest)
  | true :: rest => do
    let (a, suffix) ← parse rest
    return (some a, suffix)

def extensionBits (bins : Nat) (r : RawInstance) (fixed : List (Option Nat)) : List Bool :=
  natBits bins ++ rawInstanceBits r ++ listBits (optionBits natBits) fixed

def parseAssignments : Parser (List Nat) := parseList parseNat

def parseRawPacking : Parser RawPacking := fun input => do
  let (bins, rest) ← parseNat input
  let (assignments, suffix) ← parseAssignments rest
  return (⟨bins, assignments⟩, suffix)

def parseRawReductionOutput : Parser RawReductionOutput :=
  parsePair parseNat parseRawInstance

def parseExtension : Parser (Nat × RawInstance × List (Option Nat)) :=
  parsePair parseNat (parsePair parseRawInstance (parseList (parseOption parseNat)))

def decodeAssignments := decode parseAssignments
def decodeRawPacking := decode parseRawPacking
def decodePackingResult := decode (parseOption parseRawPacking)
def decodeRawReductionOutput := decode parseRawReductionOutput
def decodeExtension := decode parseExtension

@[simp] theorem natBits_length (n : Nat) : (natBits n).length = 2 * n.size + 1 :=
  BinPackingCompleteness.BinaryEncoding.nameBits_length n

@[simp] theorem parseNat_natBits (n : Nat) (suffix : List Bool) :
    parseNat (natBits n ++ suffix) = some (n, suffix) :=
  BinPackingCompleteness.BinaryEncoding.parseName_encoded n suffix

@[simp] theorem listBits_length {α : Type} (encode : α → List Bool) (xs : List α) :
    (listBits encode xs).length = 1 + (xs.map fun x => 1 + (encode x).length).sum := by
  induction xs with
  | nil => simp [listBits]
  | cons x xs ih => simp [listBits, ih]; omega

theorem list_length_lt_bits_length {α : Type} (encode : α → List Bool) (xs : List α) :
    xs.length < (listBits encode xs).length := by
  induction xs with
  | nil => simp [listBits]
  | cons x xs ih => simp only [listBits, List.length_cons, List.length_append]; omega

theorem list_length_le_bits_length {α : Type} (encode : α → List Bool) (xs : List α) :
    xs.length ≤ (listBits encode xs).length :=
  Nat.le_of_lt (list_length_lt_bits_length encode xs)

@[simp] theorem pairBits_length {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (p : α × β) : (pairBits ea eb p).length = (ea p.1).length + (eb p.2).length := by
  simp [pairBits]

theorem parsePair_pairBits {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (pa : Parser α) (pb : Parser β)
    (ha : ∀ a suffix, pa (ea a ++ suffix) = some (a, suffix))
    (hb : ∀ b suffix, pb (eb b ++ suffix) = some (b, suffix))
    (p : α × β) (suffix : List Bool) :
    parsePair pa pb (pairBits ea eb p ++ suffix) = some (p, suffix) := by
  rcases p with ⟨a, b⟩
  simp [pairBits, parsePair, List.append_assoc, ha, hb]

theorem parseOption_optionBits {α : Type} (encode : α → List Bool) (parse : Parser α)
    (h : ∀ a suffix, parse (encode a ++ suffix) = some (a, suffix))
    (a : Option α) (suffix : List Bool) :
    parseOption parse (optionBits encode a ++ suffix) = some (a, suffix) := by
  cases a <;> simp [optionBits, parseOption, h]

theorem parseListAux_listBits {α : Type} (encode : α → List Bool) (parse : Parser α)
    (h : ∀ a suffix, parse (encode a ++ suffix) = some (a, suffix))
    (xs : List α) (suffix : List Bool) (fuel : Nat) (enough : xs.length < fuel) :
    parseListAux parse fuel (listBits encode xs ++ suffix) = some (xs, suffix) := by
  induction xs generalizing fuel with
  | nil =>
      cases fuel with
      | zero => simp at enough
      | succ fuel => simp [listBits, parseListAux]
  | cons x xs ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have ht : xs.length < fuel := by simpa using enough
          simp [listBits, parseListAux, List.append_assoc, h, ih fuel ht]

theorem parseList_listBits {α : Type} (encode : α → List Bool) (parse : Parser α)
    (h : ∀ a suffix, parse (encode a ++ suffix) = some (a, suffix))
    (xs : List α) (suffix : List Bool) :
    parseList parse (listBits encode xs ++ suffix) = some (xs, suffix) := by
  apply parseListAux_listBits encode parse h xs suffix
  have hlen := list_length_lt_bits_length encode xs
  simp only [List.length_append]
  omega

theorem decode_encode {α : Type} (encode : α → List Bool) (parse : Parser α)
    (h : ∀ a suffix, parse (encode a ++ suffix) = some (a, suffix)) (a : α) :
    decode parse (encode a) = some a := by
  have ha := h a []
  simp only [List.append_nil] at ha
  simp [decode, ha]

theorem encode_injective {α : Type} (encode : α → List Bool) (parse : Parser α)
    (h : ∀ a suffix, parse (encode a ++ suffix) = some (a, suffix)) :
    Function.Injective encode := by
  intro a b hab
  have hd := congrArg (decode parse) hab
  simpa only [decode_encode encode parse h, Option.some.injEq] using hd

@[simp] theorem parseRawInstance_rawInstanceBits (r : RawInstance) (suffix : List Bool) :
    parseRawInstance (rawInstanceBits r ++ suffix) = some (r, suffix) :=
  parseList_listBits _ _
    (parsePair_pairBits _ _ _ _ parseNat_natBits parseNat_natBits) r suffix

@[simp] theorem parseAssignments_assignmentBits (a : List Nat) (suffix : List Bool) :
    parseAssignments (assignmentBits a ++ suffix) = some (a, suffix) :=
  parseList_listBits _ _ parseNat_natBits a suffix

@[simp] theorem parseRawPacking_rawPackingBits (p : RawPacking) (suffix : List Bool) :
    parseRawPacking (rawPackingBits p ++ suffix) = some (p, suffix) := by
  cases p
  simp [rawPackingBits, parseRawPacking, List.append_assoc]

@[simp] theorem parseRawReductionOutput_rawReductionOutputBits
    (out : RawReductionOutput) (suffix : List Bool) :
    parseRawReductionOutput (rawReductionOutputBits out ++ suffix) = some (out, suffix) :=
  parsePair_pairBits _ _ _ _ parseNat_natBits parseRawInstance_rawInstanceBits out suffix

@[simp] theorem parseExtension_extensionBits (bins : Nat) (r : RawInstance)
    (fixed : List (Option Nat)) (suffix : List Bool) :
    parseExtension (extensionBits bins r fixed ++ suffix) = some ((bins, r, fixed), suffix) := by
  have hf := parseList_listBits (optionBits natBits) (parseOption parseNat)
    (parseOption_optionBits _ _ parseNat_natBits) fixed suffix
  simp [parseExtension, parsePair, extensionBits, List.append_assoc, hf]

@[simp] theorem decodeRawInstance_rawInstanceBits (r : RawInstance) :
    decodeRawInstance (rawInstanceBits r) = some r :=
  decode_encode _ _ parseRawInstance_rawInstanceBits r

@[simp] theorem decodeAssignments_assignmentBits (a : List Nat) :
    decodeAssignments (assignmentBits a) = some a :=
  decode_encode _ _ parseAssignments_assignmentBits a

@[simp] theorem decodeRawPacking_rawPackingBits (p : RawPacking) :
    decodeRawPacking (rawPackingBits p) = some p :=
  decode_encode _ _ parseRawPacking_rawPackingBits p

@[simp] theorem decodePackingResult_packingResultBits (p : Option RawPacking) :
    decodePackingResult (packingResultBits p) = some p :=
  decode_encode _ _ (parseOption_optionBits _ _ parseRawPacking_rawPackingBits) p

@[simp] theorem decodeRawReductionOutput_rawReductionOutputBits (out : RawReductionOutput) :
    decodeRawReductionOutput (rawReductionOutputBits out) = some out :=
  decode_encode _ _ parseRawReductionOutput_rawReductionOutputBits out

@[simp] theorem decodeExtension_extensionBits (bins : Nat) (r : RawInstance)
    (fixed : List (Option Nat)) :
    decodeExtension (extensionBits bins r fixed) = some (bins, r, fixed) := by
  have h := parseExtension_extensionBits bins r fixed []
  simp only [List.append_nil] at h
  simp [decodeExtension, decode, h]

theorem rawInstanceBits_injective : Function.Injective rawInstanceBits :=
  encode_injective _ _ parseRawInstance_rawInstanceBits

theorem rawPackingBits_injective : Function.Injective rawPackingBits :=
  encode_injective _ _ parseRawPacking_rawPackingBits

@[simp] theorem rawInstanceBits_length (r : RawInstance) :
    (rawInstanceBits r).length =
      1 + (r.map fun q => 2 * q.1.size + 2 * q.2.size + 3).sum := by
  simp only [rawInstanceBits, listBits_length, pairBits_length, natBits_length]
  congr 2
  apply List.map_congr_left
  intro q _
  omega

@[simp] theorem assignmentBits_length (a : List Nat) :
    (assignmentBits a).length = 1 + (a.map fun j => 2 * j.size + 2).sum := by
  simp only [assignmentBits, listBits_length, natBits_length]
  congr 2
  apply List.map_congr_left
  intro j _
  omega

def ParserSound {α : Type} (encode : α → List Bool) (parse : Parser α) : Prop :=
  ∀ {input a suffix}, parse input = some (a, suffix) → input = encode a ++ suffix

private theorem parseFrame_sound {input bits suffix : List Bool}
    (h : BinPackingCompleteness.BinaryEncoding.parseFrame input = some (bits, suffix)) :
    input = BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix := by
  induction input using List.twoStepInduction generalizing bits suffix with
  | nil => simp [BinPackingCompleteness.BinaryEncoding.parseFrame] at h
  | singleton flag =>
      cases flag with
      | false =>
          simp only [BinPackingCompleteness.BinaryEncoding.parseFrame, Option.some.injEq,
            Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | true => simp [BinPackingCompleteness.BinaryEncoding.parseFrame] at h
  | cons_cons flag bit rest ih _ =>
      cases flag with
      | false =>
          simp only [BinPackingCompleteness.BinaryEncoding.parseFrame, Option.some.injEq,
            Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | true =>
          cases hp : BinPackingCompleteness.BinaryEncoding.parseFrame rest with
          | none => simp [BinPackingCompleteness.BinaryEncoding.parseFrame, hp] at h
          | some result =>
              rcases result with ⟨digits, tail⟩
              simp only [BinPackingCompleteness.BinaryEncoding.parseFrame, hp] at h
              rcases h with ⟨rfl, rfl⟩
              simp [BinPackingCompleteness.BinaryEncoding.frame, ih hp]

theorem parseNat_sound : ParserSound natBits parseNat := by
  intro input n suffix h
  cases hp : BinPackingCompleteness.BinaryEncoding.parseFrame input with
  | none => simp [parseNat, BinPackingCompleteness.BinaryEncoding.parseName, hp] at h
  | some result =>
      rcases result with ⟨digits, tail⟩
      by_cases hc : digits = (BinPackingCompleteness.BinaryEncoding.bitsValue digits).bits
      · have parsed : parseNat input =
            some (BinPackingCompleteness.BinaryEncoding.bitsValue digits, tail) := by
          rw [parseNat, BinPackingCompleteness.BinaryEncoding.parseName, hp]
          change (if digits = (BinPackingCompleteness.BinaryEncoding.bitsValue digits).bits
            then some (BinPackingCompleteness.BinaryEncoding.bitsValue digits, tail) else none) = _
          exact ite_eq_left hc
        have values := Option.some.inj (parsed.symm.trans h)
        simp only [Prod.mk.injEq] at values
        rcases values with ⟨rfl, rfl⟩
        simpa only [natBits, BinPackingCompleteness.BinaryEncoding.nameBits, ← hc] using
          parseFrame_sound hp
      · simp [parseNat, BinPackingCompleteness.BinaryEncoding.parseName, hp, hc] at h

theorem parsePair_sound {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (pa : Parser α) (pb : Parser β) (ha : ParserSound ea pa) (hb : ParserSound eb pb) :
    ParserSound (pairBits ea eb) (parsePair pa pb) := by
  intro input p suffix h
  cases hpa : pa input with
  | none => simp [parsePair, hpa] at h
  | some first =>
      rcases first with ⟨a, rest⟩
      cases hpb : pb rest with
      | none => simp [parsePair, hpa, hpb] at h
      | some second =>
          rcases second with ⟨b, tail⟩
          have parsed : parsePair pa pb input = some ((a, b), tail) := by
            simp [parsePair, hpa, hpb]
          have values := Option.some.inj (parsed.symm.trans h)
          simp only [Prod.mk.injEq] at values
          rcases values with ⟨rfl, rfl⟩
          rw [ha hpa, hb hpb]
          simp [pairBits, List.append_assoc]

theorem parseOption_sound {α : Type} (encode : α → List Bool) (parse : Parser α)
    (hp : ParserSound encode parse) : ParserSound (optionBits encode) (parseOption parse) := by
  intro input a suffix h
  cases input with
  | nil => simp [parseOption] at h
  | cons flag rest =>
      cases flag with
      | false =>
          simp only [parseOption, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | true =>
          cases hparse : parse rest with
          | none => simp [parseOption, hparse] at h
          | some result =>
              rcases result with ⟨x, tail⟩
              simp only [parseOption, hparse] at h
              rcases h with ⟨rfl, rfl⟩
              simp [optionBits, hp hparse]

theorem parseListAux_sound {α : Type} (encode : α → List Bool) (parse : Parser α)
    (hp : ParserSound encode parse) (fuel : Nat) :
    ParserSound (listBits encode) (parseListAux parse fuel) := by
  induction fuel with
  | zero => intro input xs suffix h; simp [parseListAux] at h
  | succ fuel ih =>
      intro input xs suffix h
      cases input with
      | nil => simp [parseListAux] at h
      | cons flag rest =>
          cases flag with
          | false =>
              simp only [parseListAux, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              rfl
          | true =>
              cases hhead : parse rest with
              | none => simp [parseListAux, hhead] at h
              | some first =>
                  rcases first with ⟨a, remaining⟩
                  cases htail : parseListAux parse fuel remaining with
                  | none => simp [parseListAux, hhead, htail] at h
                  | some second =>
                      rcases second with ⟨as, tail⟩
                      have parsed : parseListAux parse (fuel + 1) (true :: rest) =
                          some (a :: as, tail) := by
                        simp [parseListAux, hhead, htail]
                      have values := Option.some.inj (parsed.symm.trans h)
                      simp only [Prod.mk.injEq] at values
                      rcases values with ⟨rfl, rfl⟩
                      simp [listBits, hp hhead, ih htail, List.append_assoc]

theorem parseList_sound {α : Type} (encode : α → List Bool) (parse : Parser α)
    (hp : ParserSound encode parse) : ParserSound (listBits encode) (parseList parse) := by
  intro input xs suffix h
  exact parseListAux_sound encode parse hp input.length h

theorem decode_sound {α : Type} (encode : α → List Bool) (parse : Parser α)
    (hp : ParserSound encode parse) {input : List Bool} {a : α}
    (h : decode parse input = some a) : input = encode a := by
  cases hparse : parse input with
  | none => simp [decode, hparse] at h
  | some result =>
      rcases result with ⟨x, suffix⟩
      cases suffix with
      | nil =>
          simp [decode, hparse] at h
          subst x
          simpa using hp hparse
      | cons bit rest => simp [decode, hparse] at h

theorem parseRawInstance_sound : ParserSound rawInstanceBits parseRawInstance :=
  parseList_sound _ _ (parsePair_sound _ _ _ _ parseNat_sound parseNat_sound)

theorem parseAssignments_sound : ParserSound assignmentBits parseAssignments :=
  parseList_sound _ _ parseNat_sound

theorem decodeRawInstance_sound {input : List Bool} {r : RawInstance}
    (h : decodeRawInstance input = some r) : input = rawInstanceBits r :=
  decode_sound _ _ parseRawInstance_sound h

theorem decodeAssignments_sound {input : List Bool} {a : List Nat}
    (h : decodeAssignments input = some a) : input = assignmentBits a :=
  decode_sound _ _ parseAssignments_sound h

theorem decodeExtension_sound {input : List Bool} {bins : Nat} {r : RawInstance}
    {fixed : List (Option Nat)} (h : decodeExtension input = some (bins, r, fixed)) :
    input = extensionBits bins r fixed := by
  have hs : ParserSound
      (pairBits natBits (pairBits rawInstanceBits (listBits (optionBits natBits))))
      parseExtension := parsePair_sound natBits
    (pairBits rawInstanceBits (listBits (optionBits natBits))) _ _ parseNat_sound
    (parsePair_sound _ _ _ _ parseRawInstance_sound
      (parseList_sound _ _ (parseOption_sound _ _ parseNat_sound)))
  have hi := decode_sound _ _ hs h
  simpa [pairBits, extensionBits, List.append_assoc] using hi

end BinPackingGap.BinaryEncoding

namespace BinPackingGap

namespace GraphInput

def endpointPairs (G : GraphInput) : List (Nat × Nat) :=
  G.edges.map (fun edge => (edge.1.val, edge.2.val))

@[simp] theorem endpointPairs_length (G : GraphInput) :
    G.endpointPairs.length = G.edges.length := by
  simp [endpointPairs]

theorem endpointValues_injective (n : Nat) :
    Function.Injective (fun edge : Fin n × Fin n => (edge.1.val, edge.2.val)) := by
  intro a b h
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

theorem ext_of_endpointPairs (G H : GraphInput) (hn : G.n = H.n)
    (hedges : G.endpointPairs = H.endpointPairs) : G = H := by
  cases G with
  | mk n edges ordered distinct =>
      cases H with
      | mk n' edges' ordered' distinct' =>
          dsimp at hn
          cases hn
          have he : edges = edges' :=
            (endpointValues_injective n).list_map hedges
          cases he
          rfl

end GraphInput

structure GraphReductionInput where
  graph : GraphInput
  k : Nat
  k_le : k ≤ graph.n
  nonempty : graph.edges ≠ []

structure GraphFields where
  k : Nat
  vertices : List Nat
  endpoints : List (Nat × Nat)
  deriving DecidableEq

namespace GraphFields

open BinaryEncoding

def bits (fields : GraphFields) : List Bool :=
  natBits fields.k ++ listBits natBits fields.vertices ++
    listBits (pairBits natBits natBits) fields.endpoints

def parse (input : List Bool) : Option (GraphFields × List Bool) := do
  let (k, input) ← parseNat input
  let (vertices, input) ← parseList parseNat input
  let (endpoints, rest) ← parseList (parsePair parseNat parseNat) input
  return (⟨k, vertices, endpoints⟩, rest)

@[simp] theorem parse_bits (fields : GraphFields) (suffix : List Bool) :
    parse (fields.bits ++ suffix) = some (fields, suffix) := by
  have hv := parseList_listBits natBits parseNat parseNat_natBits fields.vertices
    (listBits (pairBits natBits natBits) fields.endpoints ++ suffix)
  have he := parseList_listBits (pairBits natBits natBits)
    (parsePair parseNat parseNat)
    (parsePair_pairBits _ _ _ _ parseNat_natBits parseNat_natBits)
    fields.endpoints suffix
  cases fields
  simp [parse, bits, List.append_assoc, hv, he]

def decode : List Bool → Option GraphFields := BinaryEncoding.decode parse

@[simp] theorem decode_bits (fields : GraphFields) :
    decode fields.bits = some fields :=
  decode_encode bits parse parse_bits fields

theorem bits_injective : Function.Injective bits :=
  encode_injective bits parse parse_bits

@[simp] theorem bits_length (fields : GraphFields) :
    fields.bits.length = (natBits fields.k).length +
      (listBits natBits fields.vertices).length +
      (listBits (pairBits natBits natBits) fields.endpoints).length := by
  simp [bits, Nat.add_assoc]

theorem vertices_length_le_bits (fields : GraphFields) :
    fields.vertices.length ≤ fields.bits.length := by
  have h := list_length_le_bits_length natBits fields.vertices
  rw [bits_length]
  omega

theorem endpoints_length_le_bits (fields : GraphFields) :
    fields.endpoints.length ≤ fields.bits.length := by
  have h := list_length_le_bits_length (pairBits natBits natBits) fields.endpoints
  rw [bits_length]
  omega

end GraphFields

namespace GraphReductionInput

def fields (input : GraphReductionInput) : GraphFields :=
  ⟨input.k, List.range input.graph.n, input.graph.endpointPairs⟩

@[simp] theorem fields_k (input : GraphReductionInput) : input.fields.k = input.k := rfl

@[simp] theorem fields_vertices (input : GraphReductionInput) :
    input.fields.vertices = List.range input.graph.n := rfl

@[simp] theorem fields_endpoints (input : GraphReductionInput) :
    input.fields.endpoints = input.graph.endpointPairs := rfl

theorem fields_injective : Function.Injective fields := by
  intro input other h
  have hn : input.graph.n = other.graph.n := by
    have hv := congrArg (fun f : GraphFields => f.vertices.length) h
    simpa [fields] using hv
  have he : input.graph.endpointPairs = other.graph.endpointPairs :=
    congrArg GraphFields.endpoints h
  have hg : input.graph = other.graph := GraphInput.ext_of_endpointPairs _ _ hn he
  have hk : input.k = other.k := congrArg GraphFields.k h
  cases input
  cases other
  cases hg
  cases hk
  rfl

end GraphReductionInput

def graphBits (input : GraphReductionInput) : List Bool := input.fields.bits

theorem graphBits_eq (input : GraphReductionInput) :
    graphBits input = BinaryEncoding.natBits input.k ++
      BinaryEncoding.listBits BinaryEncoding.natBits (List.range input.graph.n) ++
      BinaryEncoding.listBits
        (BinaryEncoding.pairBits BinaryEncoding.natBits BinaryEncoding.natBits)
        input.graph.endpointPairs := rfl

@[simp] theorem parse_graphBits (input : GraphReductionInput) (suffix : List Bool) :
    GraphFields.parse (graphBits input ++ suffix) = some (input.fields, suffix) :=
  GraphFields.parse_bits input.fields suffix

@[simp] theorem decode_graphBits (input : GraphReductionInput) :
    GraphFields.decode (graphBits input) = some input.fields :=
  GraphFields.decode_bits input.fields

theorem graphBits_injective : Function.Injective graphBits := by
  intro input other h
  exact GraphReductionInput.fields_injective (GraphFields.bits_injective h)

theorem graph_vertexCount_le_bits (input : GraphReductionInput) :
    input.graph.n ≤ (graphBits input).length := by
  simpa [graphBits, GraphReductionInput.fields] using
    GraphFields.vertices_length_le_bits input.fields

theorem graph_edgeCount_le_bits (input : GraphReductionInput) :
    input.graph.edges.length ≤ (graphBits input).length := by
  simpa [graphBits, GraphReductionInput.fields] using
    GraphFields.endpoints_length_le_bits input.fields

theorem graph_k_le_bits (input : GraphReductionInput) :
    input.k ≤ (graphBits input).length :=
  input.k_le.trans (graph_vertexCount_le_bits input)

end BinPackingGap

namespace BinPackingGap.GraphTallyMachine

open Turing
open BinPackingGap.BinaryEncoding
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

inductive Slot
  | header
  | vertex
  | edgeFirst
  | edgeSecond
  deriving DecidableEq

instance : Fintype Slot where
  elems := {.header, .vertex, .edgeFirst, .edgeSecond}
  complete slot := by cases slot <;> simp

inductive Mode
  | vertices
  | endpoints
  | name (slot : Slot)
  | digit (slot : Slot)
  | done
  deriving DecidableEq, Fintype

def afterName : Slot → Mode
  | .header => .vertices
  | .vertex => .vertices
  | .edgeFirst => .name .edgeSecond
  | .edgeSecond => .endpoints

def initial : Mode := .name .header

def transition : Mode → Bool → Mode
  | .vertices, true => .name .vertex
  | .vertices, false => .endpoints
  | .endpoints, true => .name .edgeFirst
  | .endpoints, false => .done
  | .name slot, true => .digit slot
  | .name slot, false => afterName slot
  | .digit slot, _ => .name slot
  | .done, _ => .done

def emit : Mode → Bool → List Bool
  | .vertices, bit => [bit]
  | .endpoints, bit => [bit]
  | _, _ => []

def scanOutput : Mode → List Bool → List Bool :=
  MachineTransducer.output transition emit

@[simp] theorem scanOutput_nil (mode : Mode) : scanOutput mode [] = [] := rfl

theorem scanOutput_cons (mode : Mode) (bit : Bool) (rest : List Bool) :
    scanOutput mode (bit :: rest) =
      emit mode bit ++ scanOutput (transition mode bit) rest := rfl

theorem scanOutput_done (input : List Bool) : scanOutput .done input = [] := by
  induction input with
  | nil => rfl
  | cons bit rest ih =>
      simpa only [scanOutput_cons, transition, emit, List.nil_append] using ih

theorem scanOutput_frame (slot : Slot) (bits suffix : List Bool) :
    scanOutput (.name slot) (BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix) =
      scanOutput (afterName slot) suffix := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
        scanOutput_cons, transition, emit, List.nil_append] using ih

theorem scanOutput_natBits (slot : Slot) (n : Nat) (suffix : List Bool) :
    scanOutput (.name slot) (natBits n ++ suffix) =
      scanOutput (afterName slot) suffix :=
  scanOutput_frame slot n.bits suffix

theorem scanOutput_pairBits (edge : Nat × Nat) (suffix : List Bool) :
    scanOutput (.name .edgeFirst) (pairBits natBits natBits edge ++ suffix) =
      scanOutput .endpoints suffix := by
  simp only [pairBits, List.append_assoc, scanOutput_natBits, afterName]

theorem scanOutput_vertices (vertices : List Nat) (suffix : List Bool) :
    scanOutput .vertices (listBits natBits vertices ++ suffix) =
      encodeWord vertices.length ++ scanOutput .endpoints suffix := by
  induction vertices with
  | nil => rfl
  | cons vertex vertices ih =>
      simp only [listBits, List.cons_append, List.append_assoc, scanOutput_cons,
        transition, emit, scanOutput_natBits, afterName, ih, List.length_cons,
        encodeWord, List.replicate_succ, List.nil_append]

theorem scanOutput_endpoints (endpoints : List (Nat × Nat)) (suffix : List Bool) :
    scanOutput .endpoints (listBits (pairBits natBits natBits) endpoints ++ suffix) =
      encodeWord endpoints.length ++ scanOutput .done suffix := by
  induction endpoints with
  | nil => rfl
  | cons edge endpoints ih =>
      simp only [listBits, List.cons_append, List.append_assoc, scanOutput_cons,
        transition, emit, scanOutput_pairBits, ih, List.length_cons,
        encodeWord, List.replicate_succ, List.nil_append]

def fieldsTally (fields : GraphFields) : Nat × Nat :=
  (fields.vertices.length, fields.endpoints.length)

def tallyBits (counts : Nat × Nat) : List Bool :=
  encodeWord counts.1 ++ encodeWord counts.2

theorem output_graphFields (fields : GraphFields) :
    scanOutput initial fields.bits = tallyBits (fieldsTally fields) := by
  have hend := scanOutput_endpoints fields.endpoints []
  simp only [List.append_nil, scanOutput_nil] at hend
  simp only [initial, GraphFields.bits, List.append_assoc, scanOutput_natBits,
    afterName, scanOutput_vertices, hend, tallyBits, fieldsTally]

def graphTally (input : GraphReductionInput) : Nat × Nat :=
  (input.graph.n, input.graph.edges.length)

theorem fieldsTally_fields (input : GraphReductionInput) :
    fieldsTally input.fields = graphTally input := by
  simp only [fieldsTally, GraphReductionInput.fields, List.length_range,
    GraphInput.endpointPairs_length, graphTally]

theorem output_graphBits (input : GraphReductionInput) :
    scanOutput initial (graphBits input) = tallyBits (graphTally input) := by
  change scanOutput initial input.fields.bits = _
  rw [output_graphFields, fieldsTally_fields]

theorem emit_length_le (mode : Mode) (bit : Bool) : (emit mode bit).length ≤ 1 := by
  cases mode <;> simp [emit]

theorem scanOutput_length_le (mode : Mode) (input : List Bool) :
    (scanOutput mode input).length ≤ input.length := by
  induction input generalizing mode with
  | nil => exact Nat.le_refl _
  | cons bit input ih =>
      rw [scanOutput_cons, List.length_append, List.length_cons]
      have he := emit_length_le mode bit
      have hi := ih (transition mode bit)
      omega

theorem tallyBits_length_le (fields : GraphFields) :
    (tallyBits (fieldsTally fields)).length ≤ fields.bits.length := by
  rw [← output_graphFields]
  exact scanOutput_length_le initial fields.bits

def reversedMachine : FinTM2 := MachineTransducer.machine initial transition emit

theorem reversedTrace (fields : GraphFields) :
    (MachineComposition.advance reversedMachine.step)^[2 * fields.bits.length + 1]
      (some (initList reversedMachine fields.bits)) =
      some (haltList reversedMachine (tallyBits (fieldsTally fields)).reverse) := by
  have trace := MachineTransducer.transduce_init_steps initial transition emit fields.bits
  change (MachineComposition.advance reversedMachine.step)^[2 * fields.bits.length + 1]
      (some (initList reversedMachine fields.bits)) =
      some (haltList reversedMachine (scanOutput initial fields.bits).reverse) at trace
  rw [output_graphFields] at trace
  exact trace

def outputsInTime_reversed (fields : GraphFields) :
    TM2OutputsInTime reversedMachine fields.bits
      (some (tallyBits (fieldsTally fields)).reverse) (2 * fields.bits.length + 1) where
  steps := 2 * fields.bits.length + 1
  evals_in_steps := reversedTrace fields
  steps_le_m := Nat.le_refl _

def machine : FinTM2 :=
  MachineSequential.machine reversedMachine MachineReverse.machine id false

def fieldsOutputsInTime (fields : GraphFields) :
    TM2OutputsInTime machine fields.bits (some (tallyBits (fieldsTally fields)))
      (5 * fields.bits.length + 4) := by
  have second : TM2OutputsInTime MachineReverse.machine
      ((tallyBits (fieldsTally fields)).reverse.map id)
      (some (tallyBits (fieldsTally fields)))
      ((tallyBits (fieldsTally fields)).length + 1) := by
    have hmap := @List.map_id (MachineReverse.machine.Γ MachineReverse.machine.k₀)
      (tallyBits (fieldsTally fields)).reverse
    rw [hmap]
    simpa only [List.reverse_reverse, List.length_reverse] using
      MachineReverse.outputsInTime (tallyBits (fieldsTally fields)).reverse
  have run := MachineSequential.execute reversedMachine MachineReverse.machine id false
    fields.bits (tallyBits (fieldsTally fields)).reverse (tallyBits (fieldsTally fields))
    (2 * fields.bits.length + 1) ((tallyBits (fieldsTally fields)).length + 1)
    (outputsInTime_reversed fields) second
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  refine le_trans run.steps_le_m ?_
  change 2 * fields.bits.length + 1 +
    2 * ((tallyBits (fieldsTally fields)).reverse.length + 1) +
    ((tallyBits (fieldsTally fields)).length + 1) ≤ 5 * fields.bits.length + 4
  have hlen := tallyBits_length_le fields
  simp only [List.length_reverse]
  omega

def outputsInTime (input : GraphReductionInput) :
    TM2OutputsInTime machine (graphBits input) (some (tallyBits (graphTally input)))
      (5 * (graphBits input).length + 4) := by
  simpa only [fieldsTally_fields, graphBits] using fieldsOutputsInTime input.fields

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime graphBits tallyBits graphTally where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 5 * Polynomial.X + Polynomial.C 4
  outputsFun input := by
    change TM2OutputsInTime machine ((graphBits input).map id)
      (some ((tallyBits (graphTally input)).map id))
      ((Polynomial.C 5 * Polynomial.X + Polynomial.C 4 : Polynomial Nat).eval
        (graphBits input).length)
    have hi := @List.map_id (machine.Γ machine.k₀) (graphBits input)
    have ho := @List.map_id (machine.Γ machine.k₁) (tallyBits (graphTally input))
    rw [hi, ho]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using outputsInTime input

theorem machine_finiteAlphabet (tape : machine.K) : Finite (machine.Γ tape) := by
  rcases tape with tape | tape | tape <;> change Finite Bool <;> infer_instance

def tallyCopyInTime {K Λ σ : Type} [DecidableEq K]
    (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (scanLabel restoreLabel : Λ) (emitterLabel : Mode → Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ
      (MachineTransducerCopy.State σ Mode))
    (atScan : program scanLabel =
      MachineTransducerCopy.scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      MachineTransducerCopy.emitter destination transition emit scanLabel control symbol)
    (atRestore : program restoreLabel =
      MachineTransfer.loopAt scratch source id false restoreLabel exit)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (input : GraphReductionInput) (sourceWord : base source = graphBits input)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some scanLabel, ((ambient, initial), register), base⟩
      (some ⟨exit, ((ambient, initial), none),
        Function.update base destination
          ((tallyBits (graphTally input)).reverse ++ base destination)⟩)
      (3 * (graphBits input).length + 2) := by
  have run := MachineTransducerCopy.transduceCopyInTime
    source scratch destination sourceScratch sourceDestination scratchDestination
    initial transition emit scanLabel restoreLabel emitterLabel exit program
    atScan atEmitter atRestore base scratchEmpty ambient initial register
  have hout : MachineTransducer.output transition emit initial (base source) =
      tallyBits (graphTally input) := by
    change scanOutput initial (base source) = _
    rw [sourceWord, output_graphBits]
  rw [hout] at run
  simpa only [sourceWord] using run

end BinPackingGap.GraphTallyMachine

end OAI
