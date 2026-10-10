import Mathlib
import OAI.Computability.MaxCut.PCP.Occurrences

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open MaxCutGames.Reduction.CloneGap
open MaxCutGames.Reduction.FiniteNoise

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

/-- One local descriptor, reusing the existing folded and empty-context
equations. The first-valid search is over the fixed explicit answer encoding. -/
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

/-- A generic factorization first aligns the validity function itself, so no
unproved transport of dependent anchor subtypes is needed. -/
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

end MaxCutGames.Foundations.Hastad.SourceLocalEquation

/-! The actual global addresses use three input-dependent base registers.
Every local query contributes only a fixed finite selector and fixed offset,
so a finite control table can select a base and emit its unary offset. -/

namespace MaxCutGames.Foundations.Hastad.SourceAddressDescriptors

open Target SourceContexts SourceOccurrences SourceLocalEquation SourceLocalSignature
open SourceAddressArithmetic
open MaxCutGames.Reduction.CloneGap

abbrev Descriptor := Fin 3 × ℕ

def descriptor (u : ℕ) : LocalKey u → Descriptor
  | .inl f => (0, (((iEncoding u).function Encoding.bool).code f).val)
  | .inr (.inl g) => (1, (((jEncoding u).function Encoding.bool).code g).val)
  | .inr (.inr _) => (2, 0)

/-- Registers zero and one start the selected left and right query blocks;
register two is the single dummy address. -/
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
    MaxCutGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D p) =
      words (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (mapEquation (descriptor u) (emit u D (ofContext F p.1.1 p.1.2, p.2))) := by
  rw [sourceEquation_eq_map_emit]
  simp only [MaxCutGames.Reduction.SourceEncoding.equationWords, words, mapEquation]
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

end MaxCutGames.Foundations.Hastad.SourceAddressDescriptors

end OAI
