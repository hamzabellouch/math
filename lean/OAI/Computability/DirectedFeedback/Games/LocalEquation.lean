import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.Occurrences

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open DFVSGames.Reduction.CloneGap
open DFVSGames.Reduction.FiniteNoise

abbrev LocalKey (u : ℕ) := Cube (I u) ⊕ (Cube (J u) ⊕ Unit)
abbrev LocalInput (u D : ℕ) := Signature u × SourceTape.TestTape (I u) (J u) D

def signatureEncoding (u : ℕ) : Encoding (Signature u) :=
  let position := (Encoding.fin u).prod slotEncoding
  let fields := (position.function Encoding.bool).prod
    ((position.function (position.function Encoding.bool)).prod (slotContextEncoding u))
  ⟨fields.size, (signatureEquiv u).trans fields.code⟩

def signatureList (u : ℕ) : List (Signature u) := (signatureEncoding u).enumerate

theorem mem_signatureList (u : ℕ) (σ : Signature u) : σ ∈ signatureList u :=
  (signatureEncoding u).mem_enumerate σ

theorem signatureList_nodup (u : ℕ) : (signatureList u).Nodup :=
  (signatureEncoding u).nodup_enumerate

theorem signatureList_length (u : ℕ) :
    (signatureList u).length = (signatureEncoding u).size :=
  (signatureEncoding u).length_enumerate

def localInputEncoding (u D : ℕ) : Encoding (LocalInput u D) :=
  (signatureEncoding u).prod (testTapeEncoding u D)

def localInputs (u D : ℕ) : List (LocalInput u D) := (localInputEncoding u D).enumerate

theorem mem_localInputs (u D : ℕ) (p : LocalInput u D) : p ∈ localInputs u D :=
  (localInputEncoding u D).mem_enumerate p

theorem localInputs_nodup (u D : ℕ) : (localInputs u D).Nodup :=
  (localInputEncoding u D).nodup_enumerate

theorem localInputs_length (u D : ℕ) :
    (localInputs u D).length = (localInputEncoding u D).size :=
  (localInputEncoding u D).length_enumerate

def localKeyEncoding (u : ℕ) : Encoding (LocalKey u) :=
  ((iEncoding u).function Encoding.bool).sum
    (((jEncoding u).function Encoding.bool).sum Encoding.unit)

def emptyLocalAddress (u : ℕ) : EmptyContext.Address (leftAnchor u) → LocalKey u
  | .inl f => .inl f.val
  | .inr _ => .inr (.inr ())

def foldedLocalAddress (u : ℕ) (valid : J u → Bool)
    (j₀ : {j : J u // valid j = true}) :
    FoldedEquation.Address (leftAnchor u) j₀ → LocalKey u
  | .inl f => .inl f.val
  | .inr g => .inr (.inl (extendRestricted valid g.val))

def equationFor (u D : ℕ) (valid : J u → Bool) (π : J u → I u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (LocalKey u) :=
  match firstValid (jEncoding u) valid with
  | none => mapEquation (emptyLocalAddress u) (EmptyContext.equation (leftAnchor u) t.1)
  | some j₀ => mapEquation (foldedLocalAddress u valid j₀)
      (FoldedEquation.conditionedEquation valid π (leftAnchor u) j₀
        t.1 t.2.2 (realizedNoise t.2.1))

def equation (u D : ℕ) (σ : Signature u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (LocalKey u) :=
  equationFor u D (signatureValid σ) (signatureProjection σ) t

def emit (u D : ℕ) (p : LocalInput u D) : Equation (LocalKey u) :=
  equation u D p.1 p.2

def addressMap (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) : LocalKey u → Fin (nBits F u)
  | .inl f => (proofEncoding F u).code (.inl (v, f))
  | .inr (.inl g) => (proofEncoding F u).code (.inr (.inl (c, g)))
  | .inr (.inr _) => dummyIndex F u

theorem mapEquation_comp {A B C : Type} (g : B → C) (f : A → B) (e : Equation A) :
    mapEquation g (mapEquation f e) = mapEquation (g ∘ f) e := rfl

theorem addressMap_emptyLocalAddress (F : Formula) (u : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u) :
    addressMap F u c v ∘ emptyLocalAddress u = emptyAddress F u v := by
  funext a
  cases a <;> rfl

theorem addressMap_foldedLocalAddress (F : Formula) (u : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u) (valid : J u → Bool)
    (j₀ : {j : J u // valid j = true}) :
    addressMap F u c v ∘ foldedLocalAddress u valid j₀ =
      localAddress (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)
        v c valid (leftAnchor u) j₀ := by
  funext a
  cases a <;> rfl

theorem contextEquation_eq_map_equationFor (F : Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) :
    contextEquation F u D c v t =
      mapEquation (addressMap F u c v) (equationFor u D (validJ F c) (pi F c v) t) := by
  unfold contextEquation equationFor rightAnchor
  cases h : firstValid (jEncoding u) (validJ F c) with
  | none =>
    rw [mapEquation_comp, addressMap_emptyLocalAddress]
  | some j₀ =>
    rw [mapEquation_comp, addressMap_foldedLocalAddress]
    rfl

theorem contextEquation_eq_map (F : Formula) (u D : ℕ)
    (c : ClauseContext F u) (s : SlotContext u)
    (t : SourceTape.TestTape (I u) (J u) D) :
    contextEquation F u D c (sampledVariables F c s) t =
      mapEquation (addressMap F u c (sampledVariables F c s))
        (equation u D (ofContext F c s) t) := by
  have hv : signatureValid (ofContext F c s) = validJ F c :=
    funext (signature_validJ F c s)
  have hp : signatureProjection (ofContext F c s) = pi F c (sampledVariables F c s) :=
    funext (signature_pi F c s)
  rw [equation, hv, hp]
  exact contextEquation_eq_map_equationFor F u D c (sampledVariables F c s) t

theorem sourceEquation_eq_map_emit (F : Formula) (u D : ℕ)
    (p : SourceIndex F u D) :
    sourceEquation F u D p =
      mapEquation (addressMap F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (emit u D (ofContext F p.1.1 p.1.2, p.2)) :=
  contextEquation_eq_map F u D p.1.1 p.1.2 p.2

end DFVSGames.Foundations.Hastad.SourceLocalEquation


namespace DFVSGames.Foundations.Hastad.SourceAddressDescriptors

open Target SourceContexts SourceOccurrences SourceLocalEquation SourceLocalSignature
open SourceAddressArithmetic
open DFVSGames.Reduction.CloneGap

abbrev Descriptor := Fin 3 × ℕ

def descriptor (u : ℕ) : LocalKey u → Descriptor
  | .inl f => (0, (((iEncoding u).function Encoding.bool).code f).val)
  | .inr (.inl g) => (1, (((jEncoding u).function Encoding.bool).code g).val)
  | .inr (.inr _) => (2, 0)

def baseValue (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (side : Fin 3) : ℕ :=
  if side = 0 then 2 ^ (2 ^ u) * ((variableEncoding F u).code v).val
  else if side = 1 then F.«variables» ^ u * 2 ^ (2 ^ u) +
    2 ^ (8 ^ u) * ((clauseEncoding F u).code c).val
  else F.«variables» ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u)

def realize (base : Fin 3 → ℕ) (d : Descriptor) : ℕ := d.2 + base d.1

def words (base : Fin 3 → ℕ) (e : Equation Descriptor) : List ℕ :=
  [realize base e.first, realize base e.second, realize base e.third,
    if e.rhs then 1 else 0]

theorem realize_descriptor (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (key : LocalKey u) :
    realize (baseValue F u c v) (descriptor u key) = (addressMap F u c v key).val := by
  cases key with
  | inl f =>
      simpa [realize, descriptor, baseValue, addressMap] using
        (left_address F u v f).symm
  | inr key =>
      cases key with
      | inl g =>
          simp [realize, descriptor, baseValue, addressMap, right_address]
          omega
      | inr _dummy =>
          simp only [realize, descriptor, baseValue, show (2 : Fin 3) ≠ 0 by decide,
            show (2 : Fin 3) ≠ 1 by decide, ite_false, Nat.zero_add, addressMap,
            dummy_address]

theorem descriptor_offset_bound (u : ℕ) (key : LocalKey u) :
    (descriptor u key).2 < 2 ^ (2 ^ u) + 2 ^ (8 ^ u) + 1 := by
  cases key with
  | inl f =>
      have h := (((iEncoding u).function Encoding.bool).code f).isLt
      change _ < 2 ^ (2 ^ u) at h
      change (((iEncoding u).function Encoding.bool).code f).val < _
      calc
        _ < (2 ^ (2 ^ u) : ℕ) := h
        _ ≤ 2 ^ (2 ^ u) + 2 ^ (8 ^ u) := Nat.le_add_right _ _
        _ ≤ _ := Nat.le_add_right _ _
  | inr key =>
      cases key with
      | inl g =>
          have h := (((jEncoding u).function Encoding.bool).code g).isLt
          change _ < 2 ^ (8 ^ u) at h
          change (((jEncoding u).function Encoding.bool).code g).val < _
          calc
            _ < (2 ^ (8 ^ u) : ℕ) := h
            _ ≤ 2 ^ (2 ^ u) + 2 ^ (8 ^ u) := Nat.le_add_left _ _
            _ ≤ _ := Nat.le_add_right _ _
      | inr _dummy => simp [descriptor]

theorem sourceEquation_numeric (F : Formula) (u D : ℕ) (p : SourceIndex F u D) :
    mapEquation Fin.val (sourceEquation F u D p) =
      mapEquation (realize (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2)))
        (mapEquation (descriptor u) (emit u D (ofContext F p.1.1 p.1.2, p.2))) := by
  rw [sourceEquation_eq_map_emit, mapEquation_comp, mapEquation_comp]
  congr 1
  funext key
  exact (realize_descriptor F u p.1.1 (sampledVariables F p.1.1 p.1.2) key).symm

theorem sourceEquation_words (F : Formula) (u D : ℕ) (p : SourceIndex F u D) :
    DFVSGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D p) =
      words (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (mapEquation (descriptor u) (emit u D (ofContext F p.1.1 p.1.2, p.2))) := by
  rw [sourceEquation_eq_map_emit]
  simp only [DFVSGames.Reduction.SourceEncoding.equationWords, words, mapEquation]
  rw [realize_descriptor, realize_descriptor, realize_descriptor]
  rfl

theorem baseValue_lt (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (side : Fin 3) :
    baseValue F u c v side < nBits F u := by
  have hside : side = 0 ∨ side = 1 ∨ side = 2 := by omega
  rcases hside with rfl | rfl | rfl
  · have h := (addressMap F u c v (.inl (fun _ => false))).isLt
    rw [← realize_descriptor] at h
    change _ + baseValue F u c v 0 < _ at h
    exact (Nat.le_add_left _ _).trans_lt h
  · have h := (addressMap F u c v (.inr (.inl (fun _ => false)))).isLt
    rw [← realize_descriptor] at h
    change _ + baseValue F u c v 1 < _ at h
    exact (Nat.le_add_left _ _).trans_lt h
  · have h := (addressMap F u c v (.inr (.inr ()))).isLt
    rw [← realize_descriptor] at h
    simpa only [realize, descriptor, Nat.zero_add] using h

theorem equation_emit_steps_le (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (e : Equation Descriptor) :
    2 * (baseValue F u c v e.first.1 + baseValue F u c v e.second.1 +
      baseValue F u c v e.third.1) + 16 ≤ 6 * nBits F u + 16 := by
  have h₁ := (baseValue_lt F u c v e.first.1).le
  have h₂ := (baseValue_lt F u c v e.second.1).le
  have h₃ := (baseValue_lt F u c v e.third.1).le
  omega

end DFVSGames.Foundations.Hastad.SourceAddressDescriptors


namespace DFVSGames.Foundations.Complexity.MachineRegisterEmit

open Turing
open DFVSGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def emitStatement (destination : K) (offset : Nat) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  pushWord destination (List.replicate offset true) (finish exit)

theorem emitStep (destination : K) (offset : Nat) (emitLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atEmit : program emitLabel = emitStatement destination offset exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some emitLabel, (ambient, register), base⟩ =
      some ⟨exit, (ambient, register),
        Function.update base destination (List.replicate offset true ++ base destination)⟩ := by
  change some (TM2.stepAux (program emitLabel) (ambient, register) base) = _
  rw [atEmit, emitStatement, stepAux_pushWord]
  cases exit <;> simp [finish, TM2.stepAux]

theorem prefix_encodeWord (offset n : Nat) :
    List.replicate offset true ++ encodeWord n = encodeWord (offset + n) := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

theorem registerEmitTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (offset : Nat)
    (firstLabel secondLabel emitLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel))
    (atSecond : program secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel (some emitLabel))
    (atEmit : program emitLabel = emitStatement destination offset exit)
    (base : K → List Bool) (n : Nat) (sourceWord : base source = encodeWord n)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 5]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (offset + n) ++ base destination)⟩ := by
  have copied := MachineCopy.copyTrace source destination scratch sourceDestination
    sourceScratch destinationScratch false firstLabel secondLabel (some emitLabel)
    program atFirst atSecond base scratchEmpty ambient register
  rw [sourceWord, encodeWord_length] at copied
  rw [show 2 * n + 5 = 1 + 2 * (n + 1 + 1) by omega,
    Function.iterate_add_apply, copied, Function.iterate_one]
  change TM2.step program
    ⟨some emitLabel, (ambient, none),
      Function.update base destination (encodeWord n ++ base destination)⟩ = _
  rw [emitStep destination offset emitLabel exit program atEmit]
  simp only [Function.update_self, Function.update_idem]
  rw [← List.append_assoc, prefix_encodeWord]

def registerEmitInTime (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (offset : Nat)
    (firstLabel secondLabel emitLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel))
    (atSecond : program secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel (some emitLabel))
    (atEmit : program emitLabel = emitStatement destination offset exit)
    (base : K → List Bool) (n : Nat) (sourceWord : base source = encodeWord n)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (offset + n) ++ base destination)⟩)
      (2 * n + 5) where
  steps := 2 * n + 5
  evals_in_steps := registerEmitTrace source destination scratch sourceDestination sourceScratch
    destinationScratch offset firstLabel secondLabel emitLabel exit program atFirst atSecond
    atEmit base n sourceWord scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

def program (source destination scratch : K) (offset : Nat) (exit : Option (Fin 3)) :
    Fin 3 → TM2.Stmt (Alphabet (K := K)) (Fin 3) (σ × Option Bool) :=
  fun label => if label = 0 then
    Reduction.MachineTransfer.loopAt source scratch id false 0 (some 1)
  else if label = 1 then
    MachineCopy.forkLoop scratch source destination false 1 (some 2)
  else emitStatement destination offset exit

def programInTime (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (offset : Nat) (exit : Option (Fin 3))
    (base : K → List Bool) (n : Nat) (sourceWord : base source = encodeWord n)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program source destination scratch offset exit))
      ⟨some 0, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (offset + n) ++ base destination)⟩)
      (2 * n + 5) :=
  registerEmitInTime source destination scratch sourceDestination sourceScratch
    destinationScratch offset 0 1 2 exit (program source destination scratch offset exit)
    (by simp [program]) (by simp [program]) (by simp [program])
    base n sourceWord scratchEmpty ambient register

def machine (offset : Nat) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program 0 1 2 offset none

def machineInTime (offset : Nat) (base : Fin 3 → List Bool) (n : Nat)
    (sourceWord : base 0 = encodeWord n) (scratchEmpty : base 2 = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (machine offset).step
      ⟨some (0 : Fin 3), ((), register), base⟩
      (some ⟨none, ((), none),
        Function.update base (1 : Fin 3) (encodeWord (offset + n) ++ base 1)⟩)
      (2 * n + 5) :=
  programInTime (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    offset none base n sourceWord scratchEmpty () register

omit [DecidableEq K] in
theorem emitStatement_pushes (destination : K) (offset : Nat) (exit : Option Λ) :
    Runtime.statementPushBound (emitStatement (σ := σ) destination offset exit) = offset := by
  cases exit <;> simp [emitStatement, statementPushBound_pushWord, finish,
    Runtime.statementPushBound]

omit [DecidableEq K] in
theorem program_pushes_le (source destination scratch : K) (offset : Nat)
    (exit : Option (Fin 3)) (label : Fin 3) :
    Runtime.statementPushBound
      (program (σ := σ) source destination scratch offset exit label) ≤ max 2 offset := by
  unfold program
  split
  · simp [Reduction.MachineTransfer.loopAt, Reduction.MachineTransfer.exitAt,
      Runtime.statementPushBound]
  · split
    · simp [MachineCopy.forkLoop, Reduction.MachineTransfer.exitAt,
        Runtime.statementPushBound]
    · simpa only [emitStatement_pushes] using (Nat.le_max_right 2 offset)

theorem machine_pushes_le (offset : Nat) :
    Runtime.programPushBound (machine offset) ≤ max 2 offset := by
  have h : ∀ labels : List (Fin 3),
      Runtime.maxLabelPushes (machine offset).m labels ≤ max 2 offset := by
    intro labels
    change Runtime.maxLabelPushes (program (σ := Unit) (0 : Fin 3) 1 2 offset none)
      labels ≤ max 2 offset
    induction labels with
    | nil => exact Nat.zero_le _
    | cons label labels ih =>
      exact max_le (program_pushes_le (σ := Unit) (0 : Fin 3) 1 2 offset none label) ih
  exact h _

end DFVSGames.Foundations.Complexity.MachineRegisterEmit


namespace DFVSGames.Foundations.Hastad.SourceEquationEmit

open Turing Complexity
open SourceAddressDescriptors
open DFVSGames.Reduction.CloneGap
open DFVSGames.Reduction.MachineSubstitution

inductive Label
  | seed | thirdDrain | thirdFork | thirdEmit
  | secondDrain | secondFork | secondEmit | firstDrain | firstFork | firstEmit
  deriving DecidableEq

instance instFintypeLabel : Fintype Label := derive_fintype% _

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool

def rhsBit (e : Equation Descriptor) : Nat := if e.rhs then 1 else 0

def steps (values : Fin 3 → Nat) (e : Equation Descriptor) : Nat :=
  2 * (values e.first.1 + values e.second.1 + values e.third.1) + 16

variable {K Λ σ : Type} [DecidableEq K]

def statement (sources : Fin 3 → K) (destination scratch : K)
    (e : Equation Descriptor) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .seed => pushWord destination (encodeWord (rhsBit e)).reverse
      (.goto fun _ => labels .thirdDrain)
  | .thirdDrain => Reduction.MachineTransfer.loopAt (sources e.third.1) scratch id false
      (labels .thirdDrain) (some (labels .thirdFork))
  | .thirdFork => MachineCopy.forkLoop scratch (sources e.third.1) destination false
      (labels .thirdFork) (some (labels .thirdEmit))
  | .thirdEmit => MachineRegisterEmit.emitStatement destination e.third.2
      (some (labels .secondDrain))
  | .secondDrain => Reduction.MachineTransfer.loopAt (sources e.second.1) scratch id false
      (labels .secondDrain) (some (labels .secondFork))
  | .secondFork => MachineCopy.forkLoop scratch (sources e.second.1) destination false
      (labels .secondFork) (some (labels .secondEmit))
  | .secondEmit => MachineRegisterEmit.emitStatement destination e.second.2
      (some (labels .firstDrain))
  | .firstDrain => Reduction.MachineTransfer.loopAt (sources e.first.1) scratch id false
      (labels .firstDrain) (some (labels .firstFork))
  | .firstFork => MachineCopy.forkLoop scratch (sources e.first.1) destination false
      (labels .firstFork) (some (labels .firstEmit))
  | .firstEmit => MachineRegisterEmit.emitStatement destination e.first.2 exit

def program (sources : Fin 3 → K) (destination scratch : K) (e : Equation Descriptor) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (State σ) :=
  statement sources destination scratch e id none

def prefixTapes (destination : K) (base : K → List Bool) (written : List Nat) :
    K → List Bool := Function.update base destination (encodeWords written ++ base destination)

theorem prefixTapes_other (destination : K) (base : K → List Bool) (written : List Nat)
    (k : K) (hk : k ≠ destination) : prefixTapes destination base written k = base k := by
  simp [prefixTapes, hk]

theorem equationTrace (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (e : Equation Descriptor)
    (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement sources destination scratch e labels exit label)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps values e]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩ := by
  have hw (written : List Nat) (side : Fin 3) :
      prefixTapes destination base written (sources side) = encodeWord (values side) := by
    rw [prefixTapes_other _ _ _ _ (sourceDestination side), sourceWords side]
  have hs (written : List Nat) : prefixTapes destination base written scratch = [] := by
    rw [prefixTapes_other _ _ _ _ (Ne.symm destinationScratch), scratchEmpty]
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨some (labels .thirdDrain), (ambient, register),
        prefixTapes destination base [rhsBit e]⟩ := by
    change some (TM2.stepAux (p (labels .seed)) (ambient, register) base) = _
    rw [atLabels .seed]
    simp only [statement, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
      prefixTapes, encodeWords, List.append_nil]
  have hthird : (MachineComposition.advance (TM2.step p))^[2 * values e.third.1 + 5]
      (some ⟨some (labels .thirdDrain), (ambient, register),
        prefixTapes destination base [rhsBit e]⟩) =
      some ⟨some (labels .secondDrain), (ambient, none),
        prefixTapes destination base [realize values e.third, rhsBit e]⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.third.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.third.2
      (labels .thirdDrain) (labels .thirdFork) (labels .thirdEmit) (some (labels .secondDrain))
      p (atLabels .thirdDrain) (atLabels .thirdFork) (atLabels .thirdEmit)
      (prefixTapes destination base [rhsBit e]) (values e.third.1)
      (hw _ _) (hs _) ambient register
    simpa only [prefixTapes, Function.update_self, Function.update_idem, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  have hsecond : (MachineComposition.advance (TM2.step p))^[2 * values e.second.1 + 5]
      (some ⟨some (labels .secondDrain), (ambient, none),
        prefixTapes destination base [realize values e.third, rhsBit e]⟩) =
      some ⟨some (labels .firstDrain), (ambient, none),
        prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e]⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.second.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.second.2
      (labels .secondDrain) (labels .secondFork) (labels .secondEmit) (some (labels .firstDrain))
      p (atLabels .secondDrain) (atLabels .secondFork) (atLabels .secondEmit)
      (prefixTapes destination base [realize values e.third, rhsBit e]) (values e.second.1)
      (hw _ _) (hs _) ambient none
    simpa only [prefixTapes, Function.update_self, Function.update_idem, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  have hfirst : (MachineComposition.advance (TM2.step p))^[2 * values e.first.1 + 5]
      (some ⟨some (labels .firstDrain), (ambient, none),
        prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e]⟩) =
      some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.first.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.first.2
      (labels .firstDrain) (labels .firstFork) (labels .firstEmit) exit
      p (atLabels .firstDrain) (atLabels .firstFork) (atLabels .firstEmit)
      (prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e])
      (values e.first.1) (hw _ _) (hs _) ambient none
    simpa only [prefixTapes, Function.update_self, Function.update_idem, words, rhsBit, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  rw [show steps values e = (2 * values e.first.1 + 5) +
      ((2 * values e.second.1 + 5) + ((2 * values e.third.1 + 5) + 1)) by
        unfold steps; omega]
  rw [Function.iterate_add_apply _ (2 * values e.first.1 + 5),
    Function.iterate_add_apply _ (2 * values e.second.1 + 5),
    Function.iterate_add_apply _ (2 * values e.third.1 + 5), hseed, hthird, hsecond, hfirst]

def equationInTime (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (e : Equation Descriptor)
    (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement sources destination scratch e labels exit label)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩)
      (steps values e) where
  steps := steps values e
  evals_in_steps := equationTrace sources destination scratch sourceDestination sourceScratch
    destinationScratch e labels exit p atLabels base values sourceWords scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

def programInTime (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (e : Equation Descriptor)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (σ := σ) sources destination scratch e))
      ⟨some .seed, (ambient, register), base⟩
      (some ⟨none, (ambient, none), prefixTapes destination base (words values e)⟩)
      (steps values e) :=
  equationInTime sources destination scratch sourceDestination sourceScratch destinationScratch
    e id none (program sources destination scratch e) (fun _ => rfl)
    base values sourceWords scratchEmpty ambient register

abbrev Tape := Fin 3 ⊕ Bool

def machine (e : Equation Descriptor) : FinTM2 where
  K := Tape
  k₀ := .inl 0
  k₁ := .inr false
  Γ _ := Bool
  Λ := Label
  main := .seed
  σ := State Unit
  initialState := ((), none)
  m := program Sum.inl (.inr false) (.inr true) e

def machineInTime (e : Equation Descriptor) (base : Tape → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (.inl side) = encodeWord (values side))
    (scratchEmpty : base (.inr true) = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine e).step
      ⟨some Label.seed, ((), register), base⟩
      (some ⟨none, ((), none), prefixTapes (.inr false : Tape) base (words values e)⟩)
      (steps values e) :=
  programInTime Sum.inl (.inr false : Tape) (.inr true)
    (fun _ => Sum.inl_ne_inr) (fun _ => Sum.inl_ne_inr) (by decide)
    e base values sourceWords scratchEmpty () register

end DFVSGames.Foundations.Hastad.SourceEquationEmit


namespace DFVSGames.Foundations.Complexity.MachineFiniteTable

open Turing
open DFVSGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K] [DecidableEq σ]
variable {Γ : K → Type}

def dispatch (dst : K) (table : σ → List (Γ dst))
    (next : TM2.Stmt Γ Λ σ) : List σ → TM2.Stmt Γ Λ σ
  | [] => next
  | key :: rest =>
      .branch (fun state => decide (state = key))
        (pushWord dst (table key).reverse next) (dispatch dst table next rest)

theorem stepAux_dispatch (dst : K) (table : σ → List (Γ dst))
    (next : TM2.Stmt Γ Λ σ) (keys : List σ) (state : σ)
    (hstate : state ∈ keys) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (dispatch dst table next keys) state tapes =
      TM2.stepAux next state (Function.update tapes dst (table state ++ tapes dst)) := by
  induction keys with
  | nil => simp at hstate
  | cons key rest ih =>
      by_cases h : state = key
      · subst state
        simp only [dispatch, TM2.stepAux, decide_true, Bool.cond_true]
        simpa only [List.reverse_reverse] using
          stepAux_pushWord dst (table key).reverse next key tapes
      · have hm : state ∈ rest := (List.mem_cons.mp hstate).resolve_left h
        simpa only [dispatch, TM2.stepAux, h, decide_false, Bool.cond_false] using ih hm

omit [DecidableEq K] in

theorem dispatch_push_bound (dst : K) (table : σ → List (Γ dst))
    (next : TM2.Stmt Γ Λ σ) (keys : List σ) :
    Runtime.statementPushBound (dispatch dst table next keys) ≤
      (keys.map (fun state => (table state).length)).sum +
        Runtime.statementPushBound next := by
  induction keys with
  | nil => simp [dispatch]
  | cons key rest ih =>
      simp only [dispatch, Runtime.statementPushBound, statementPushBound_pushWord,
        List.length_reverse, List.map_cons, List.sum_cons]
      apply max_le <;> omega

def emit (dst : K) (table : σ → List (Γ dst)) (keys : List σ)
    (next : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ σ :=
  dispatch dst table next keys

def tableBound (dst : K) (table : σ → List (Γ dst)) (keys : List σ) : ℕ :=
  (keys.map (fun state => (table state).length)).sum

theorem stepAux_emit (dst : K) (table : σ → List (Γ dst))
    (keys : List σ) (hkeys : ∀ state, state ∈ keys) (next : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (emit dst table keys next) state tapes =
      TM2.stepAux next state (Function.update tapes dst (table state ++ tapes dst)) :=
  stepAux_dispatch dst table next keys state (hkeys state) tapes

omit [DecidableEq K] in
theorem emit_push_bound (dst : K) (table : σ → List (Γ dst))
    (keys : List σ) (next : TM2.Stmt Γ Λ σ) :
    Runtime.statementPushBound (emit dst table keys next) ≤
      tableBound dst table keys + Runtime.statementPushBound next :=
  dispatch_push_bound dst table next _

def emitInTime (dst : K) (table : σ → List (Γ dst))
    (keys : List σ) (hkeys : ∀ state, state ∈ keys)
    (program : Λ → TM2.Stmt Γ Λ σ) (label exitLabel : Λ)
    (atLabel : program label = emit dst table keys (.goto (fun _ => exitLabel)))
    (state : σ) (tapes : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label, state, tapes⟩
      (some ⟨some exitLabel, state,
        Function.update tapes dst (table state ++ tapes dst)⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program label) state tapes) = _
    rw [atLabel, stepAux_emit dst table keys hkeys]
    rfl
  steps_le_m := Nat.le_refl _

omit [DecidableEq σ] in
theorem output_frame (dst : K) (table : σ → List (Γ dst))
    (state : σ) (tapes : ∀ k, List (Γ k)) (k : K) (h : k ≠ dst) :
    (Function.update tapes dst (table state ++ tapes dst)) k = tapes k := by
  simp [Function.update, h]

end DFVSGames.Foundations.Complexity.MachineFiniteTable


namespace DFVSGames.Foundations.Hastad.SourceDescriptorEmission

open Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open DFVSGames.Reduction.CloneGap
open DFVSGames.Foundations.Complexity

def codedEquation (u D : ℕ) (state : LocalInput u D) :
    Equation (Fin (localKeyEncoding u).size) :=
  mapEquation (localKeyEncoding u).code (SourceLocalEquation.emit u D state)

def descriptorWords (u D : ℕ) (state : LocalInput u D) : List ℕ :=
  DFVSGames.Reduction.SourceEncoding.equationWords (codedEquation u D state)

def descriptorBits (u D : ℕ) (state : LocalInput u D) : List Bool :=
  encodeWords (descriptorWords u D state)

@[simp] theorem descriptorWords_length (u D : ℕ) (state : LocalInput u D) :
    (descriptorWords u D state).length = 4 :=
  DFVSGames.Reduction.SourceEncoding.equationWords_length _

theorem descriptorBits_length_le (u D : ℕ) (state : LocalInput u D) :
    (descriptorBits u D state).length ≤ 3 * (localKeyEncoding u).size + 2 :=
  DFVSGames.Reduction.SourceEncoding.equationBits_length_le _

@[simp] theorem decode_descriptorBits (u D : ℕ) (state : LocalInput u D) :
    decodeWords (descriptorBits u D state) = some (descriptorWords u D state) :=
  decodeWords_encodeWords _

@[simp] theorem parse_descriptorWords (u D : ℕ) (state : LocalInput u D) :
    DFVSGames.Reduction.SourceEncoding.parseEquation (localKeyEncoding u).size
      (descriptorWords u D state) = some (codedEquation u D state, []) := by
  simpa only [List.append_nil, descriptorWords] using
    DFVSGames.Reduction.SourceEncoding.parseEquation_encoded (codedEquation u D state) []

theorem decode_codedEquation (u D : ℕ) (state : LocalInput u D) :
    mapEquation (localKeyEncoding u).code.symm (codedEquation u D state) =
      SourceLocalEquation.emit u D state := by
  unfold codedEquation
  rw [SourceLocalEquation.mapEquation_comp]
  have h : (localKeyEncoding u).code.symm ∘ (localKeyEncoding u).code = id := by
    funext key
    exact (localKeyEncoding u).code.symm_apply_apply key
  rw [h]
  rfl

theorem codedEquation_global (F : Formula) (u D : ℕ) (p : SourceIndex F u D) :
    mapEquation
      (addressMap F u p.1.1 (sampledVariables F p.1.1 p.1.2) ∘
        (localKeyEncoding u).code.symm)
      (codedEquation u D (ofContext F p.1.1 p.1.2, p.2)) =
      sourceEquation F u D p := by
  rw [← SourceLocalEquation.mapEquation_comp, decode_codedEquation]
  exact (sourceEquation_eq_map_emit F u D p).symm

def descriptorPushBound (u D : ℕ) : ℕ :=
  ((localInputs u D).map (fun state => (descriptorBits u D state).length)).sum

theorem descriptorPushBound_le (u D : ℕ) :
    descriptorPushBound u D ≤
      (localInputs u D).length * (3 * (localKeyEncoding u).size + 2) := by
  have hlist (states : List (LocalInput u D)) :
      (states.map (fun state => (descriptorBits u D state).length)).sum ≤
        states.length * (3 * (localKeyEncoding u).size + 2) := by
    induction states with
    | nil => simp
    | cons state states ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      have hstate := descriptorBits_length_le u D state
      omega
  exact hlist (localInputs u D)


variable {K Λ : Type} [DecidableEq K]

instance localInputDecidableEq (u D : ℕ) : DecidableEq (LocalInput u D) :=
  fun x y =>
    if h : (localInputEncoding u D).code x = (localInputEncoding u D).code y then
      isTrue ((localInputEncoding u D).code.injective h)
    else isFalse (fun hxy => h (congrArg (localInputEncoding u D).code hxy))

def emitDescriptor (u D : ℕ) (dst : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (LocalInput u D)) :
    TM2.Stmt (fun _ : K => Bool) Λ (LocalInput u D) :=
  MachineFiniteTable.emit (Γ := fun _ : K => Bool) dst
    (descriptorBits u D) (localInputs u D) next

theorem stepAux_emitDescriptor (u D : ℕ) (dst : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (LocalInput u D))
    (state : LocalInput u D) (tapes : K → List Bool) :
    TM2.stepAux (emitDescriptor u D dst next) state tapes =
      TM2.stepAux next state
        (Function.update tapes dst (descriptorBits u D state ++ tapes dst)) :=
  MachineFiniteTable.stepAux_emit (Γ := fun _ : K => Bool) dst
    (descriptorBits u D) (localInputs u D)
    (mem_localInputs u D) next state tapes

omit [DecidableEq K] in
theorem emitDescriptor_push_bound (u D : ℕ) (dst : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (LocalInput u D)) :
    Runtime.statementPushBound (emitDescriptor u D dst next) ≤
      descriptorPushBound u D + Runtime.statementPushBound next :=
  MachineFiniteTable.emit_push_bound (Γ := fun _ : K => Bool) dst
    (descriptorBits u D) (localInputs u D) next

def emitDescriptorInTime (u D : ℕ) (dst : K)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (LocalInput u D))
    (label exitLabel : Λ)
    (atLabel : program label = emitDescriptor u D dst (.goto (fun _ => exitLabel)))
    (state : LocalInput u D) (tapes : K → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label, state, tapes⟩
      (some ⟨some exitLabel, state,
        Function.update tapes dst (descriptorBits u D state ++ tapes dst)⟩) 1 :=
  MachineFiniteTable.emitInTime (Γ := fun _ : K => Bool) dst
    (descriptorBits u D) (localInputs u D)
    (mem_localInputs u D) program label exitLabel atLabel state tapes

theorem descriptor_output_frame (u D : ℕ) (dst : K)
    (state : LocalInput u D) (tapes : K → List Bool) (k : K) (h : k ≠ dst) :
    (Function.update tapes dst (descriptorBits u D state ++ tapes dst)) k = tapes k :=
  MachineFiniteTable.output_frame (Γ := fun _ : K => Bool) dst
    (descriptorBits u D) state tapes k h


end DFVSGames.Foundations.Hastad.SourceDescriptorEmission

end OAI
