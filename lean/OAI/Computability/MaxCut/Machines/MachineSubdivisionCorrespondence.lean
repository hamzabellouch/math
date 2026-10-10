import Mathlib
import OAI.Computability.MaxCut.Machines.MachineSubdivisionTableRead
import OAI.Computability.MaxCut.Encoding.SubdivisionEncoding

namespace OAI

/-! The actual streamed bytes coincide with the numbered semantic subdivision.
The controller copies the last table unchanged, so its input contract explicitly
requires involutive tables; binary translations satisfy this condition. -/

namespace MaxCutGames.Explicit.MachineSubdivisionCorrespondence

open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionLoopFrame

def Involutive {q : Nat} (H : Instance q) : Prop :=
  ∀ e : Fin H.constraints.length,
    MachineSubdivisionRows.inverseTable H.constraints[e].permutation = H.constraints[e].permutation

theorem inverseTable_eq {q : Nat} (p : PermutationTable q)
    (same : p.inverseImages = p.images) : MachineSubdivisionRows.inverseTable p = p := by
  cases p with
  | mk images inverseImages left right =>
    dsimp at same
    cases same
    rfl

theorem translations_involutive {q s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s) (H : Instance q)
    (translations : Integration.TranslationTarget.IsTranslationInstance coordinates H) :
    Involutive H := by
  intro e
  apply inverseTable_eq
  apply Vector.ext
  intro i hi
  apply coordinates.injective
  obtain ⟨shift, law⟩ := translations H.constraints[e] (List.getElem_mem e.isLt)
  have h := law (H.constraints[e].permutation.inverseImages[(⟨i, hi⟩ : Fin q)])
  rw [H.constraints[e].permutation.rightInverse] at h
  have cancel : shift + shift = 0 := by
    ext j
    simp [CharTwo.add_self_eq_zero]
  have doubled := congrArg (fun x => x + shift) h
  have inverseLaw : coordinates (H.constraints[e].permutation.inverseImages[(⟨i, hi⟩ : Fin q)]) =
      coordinates ⟨i, hi⟩ + shift := by
    simpa only [add_assoc, cancel, add_zero] using doubled.symm
  exact inverseLaw.trans (law ⟨i, hi⟩).symm

theorem rowBits_eq_semantic {q : Nat} (H : Instance q) (e : Fin H.constraints.length)
    (involutive : Involutive H) :
    rowBits H.constraints.length e.val H.constraints[e] =
      MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
        H.constraints[e].permutation := by
  have words := MachineSubdivisionBodySpec.rowBits_eq_dynamic
    (SubdivisionTarget.vertexFields H e) H.constraints[e].permutation
  have vertices (j : Fin 5) := SubdivisionTarget.vertexFields_val H e j
  simp only [MachineSubdivisionRows.subdivisionVertexWords] at vertices
  have dynamic : MachineSubdivisionDynamicRows.rowBits
      (SubdivisionTarget.vertexFields H e) H.constraints[e].permutation =
      MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
        H.constraints[e].permutation := by
    simp only [MachineSubdivisionDynamicRows.rowBits, MachineSubdivisionRows.rowBits,
      MachineSubdivisionDynamicRows.rows, MachineSubdivisionRows.rows, involutive e]
  rw [← dynamic, ← words]
  simp only [vertices, MachineSubdivisionBodySpec.rowBits, rowBits, identityBits,
    MachineSubdivisionBody.tableBits, encodeWords_append, List.append_assoc]

theorem outputRows_eq_ofFn {n q : Nat} (Q e : Nat) (edges : List (Constraint n q)) :
    outputRows Q e edges =
      (List.ofFn (fun i : Fin edges.length => rowBits Q (e + i.val) edges[i])).flatten := by
  induction edges generalizing e with
  | nil => rfl
  | cons edge edges ih =>
    rw [outputRows, ih, List.ofFn_succ]
    simp [Nat.add_comm, Nat.add_left_comm]

theorem outputRows_eq_semantic {q : Nat} (H : Instance q) (involutive : Involutive H) :
    outputRows H.constraints.length 0 H.constraints =
      (List.finRange H.constraints.length).flatMap (fun e =>
        MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
          H.constraints[e].permutation) := by
  rw [outputRows_eq_ofFn]
  simp only [Nat.zero_add, rowBits_eq_semantic H _ involutive, List.ofFn_eq_map,
    List.flatMap_def]

/-- Exact complete serialized output, including the changed headers and every
forward permutation-table entry, in occurrence order. -/
theorem output_eq_gameBits {q : Nat} (H : Instance q) (involutive : Involutive H) :
    MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
      outputRows H.constraints.length 0 H.constraints =
      gameBits (SubdivisionTarget.subdivide H) := by
  rw [SubdivisionEncoding.subdivide_gameBits, outputRows_eq_semantic H involutive]
  rfl

end MaxCutGames.Explicit.MachineSubdivisionCorrespondence

/-! The complete finite subdivision machine, including its polynomial runtime
in the actual serialized input length and exact full-table output. -/

namespace MaxCutGames.Explicit.MachineSubdivisionRuntime

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame
open MachineSubdivisionCorrespondence

noncomputable section

def prefixPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.X * (Polynomial.C 100 *
    (Polynomial.C 4 * Polynomial.X + Polynomial.C (q * (q + 1)) + 1) + 1) +
    Polynomial.C 62 * Polynomial.X + Polynomial.C (q + 50)

def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineSubdivisionFinish.timePolynomial q (prefixPolynomial q)

theorem input_eq {q : Nat} (H : Instance q) :
    gameBits H = encodeWords [H.vertices, q, H.constraints.length] ++ bodyBits H.constraints := by
  simp only [gameBits, gameWords, bodyBits, encodeWords_append]

theorem input_size {q : Nat} (H : Instance q) :
    H.vertices ≤ (gameBits H).length ∧ H.constraints.length ≤ (gameBits H).length := by
  rw [input_eq]
  simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  omega

def finalTapes {q : Nat} (H : Instance q) : Tape → List Bool :=
  frame H.constraints.length H.constraints.length ([] : List (Constraint H.vertices q))
    (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
      outputRows H.constraints.length 0 H.constraints)

theorem final_outputEmpty {q : Nat} (H : Instance q) : finalTapes H .output = [] := rfl

theorem final_accumulator {q : Nat} (H : Instance q) (involutive : Involutive H) :
    finalTapes H .accumulator = (gameBits (SubdivisionTarget.subdivide H)).reverse := by
  change (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
    outputRows H.constraints.length 0 H.constraints).reverse = _
  rw [output_eq_gameBits H involutive]

/-- The prefix contains every actual header read, fresh-name initialization,
header emission, complete four-row body, and occurrence-counter test. -/
def prefixInTime {q : Nat} (H : Instance q) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (gameBits H))
      (some ⟨some .finishStart, initialState, finalTapes H⟩)
      ((prefixPolynomial q).eval (gameBits H).length) := by
  have initial := MachineSubdivisionEmission.prepareInTime q H.vertices H.constraints.length
    (bodyBits H.constraints)
  rw [← input_eq H, ← frame_prepared H.constraints] at initial
  have loop := MachineSubdivisionLoop.loopInTime H.constraints.length 0 H.constraints
    (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length) (by simp)
  simp only [Nat.zero_add] at loop
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initial loop
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := ?_ }
  have hn := (input_size H).1
  have hQ := (input_size H).2
  have bodyBound : MachineSubdivisionLoop.bodyBound H.vertices q H.constraints.length + 1 ≤
      100 * (4 * (gameBits H).length + q * (q + 1) + 1) + 1 := by
    unfold MachineSubdivisionLoop.bodyBound
    omega
  have loopBound := Nat.mul_le_mul hQ bodyBound
  have prepBound : H.vertices + q + H.constraints.length + 6 +
      9 * MachineSubdivisionInit.stageCost H.vertices H.constraints.length +
      (3 * (H.vertices + 7 * H.constraints.length + 2) + 10) ≤
      62 * (gameBits H).length + q + 49 := by
    unfold MachineSubdivisionInit.stageCost
    omega
  have bound := whole.steps_le_m
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  omega

/-- Literal initialization to literal clean halting configuration, with exact
semantic subdivision output. No execution or runtime premise is assumed. -/
def fullRunInTime {q : Nat} (H : Instance q) (involutive : Involutive H) :
    TM2OutputsInTime (machine q) (gameBits H)
      (some (gameBits (SubdivisionTarget.subdivide H)))
      ((timePolynomial q).eval (gameBits H).length) := by
  have run := MachineSubdivisionFinish.completePrefix q (gameBits H) (prefixPolynomial q)
    (finalTapes H) (prefixInTime H) (final_outputEmpty H)
  simpa only [final_accumulator H involutive, List.reverse_reverse, timePolynomial] using run

/-- The input subtype records the mathematical involution property, while the
same finite transition program is used for every instance of the fixed alphabet. -/
def computableInPolyTime (q : Nat) :
    TM2ComputableInPolyTime
      (fun H : {H : Instance q // Involutive H} => gameBits H.val)
      gameBits (fun H => SubdivisionTarget.subdivide H.val) where
  tm := machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q
  outputsFun H := by
    change TM2OutputsInTime (machine q) ((gameBits H.val).map id)
      (some ((gameBits (SubdivisionTarget.subdivide H.val)).map id))
      ((timePolynomial q).eval (gameBits H.val).length)
    have hi := @List.map_id ((machine q).Γ (machine q).k₀) (gameBits H.val)
    have ho := @List.map_id ((machine q).Γ (machine q).k₁)
      (gameBits (SubdivisionTarget.subdivide H.val))
    erw [hi, ho]
    exact fullRunInTime H.val H.property

def familyComputableInPolyTime {α : Type} {q : Nat} (f : α → Instance q)
    (involutive : ∀ a, Involutive (f a)) :
    TM2ComputableInPolyTime (fun a => gameBits (f a)) gameBits
      (fun a => SubdivisionTarget.subdivide (f a)) where
  tm := machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q
  outputsFun a := by
    change TM2OutputsInTime (machine q) ((gameBits (f a)).map id)
      (some ((gameBits (SubdivisionTarget.subdivide (f a))).map id))
      ((timePolynomial q).eval (gameBits (f a)).length)
    have hi := @List.map_id ((machine q).Γ (machine q).k₀) (gameBits (f a))
    have ho := @List.map_id ((machine q).Γ (machine q).k₁)
      (gameBits (SubdivisionTarget.subdivide (f a)))
    erw [hi, ho]
    exact fullRunInTime (f a) (involutive a)

theorem workAlphabetFinite (q : Nat) (tape : (computableInPolyTime q).tm.K) :
    Finite ((computableInPolyTime q).tm.Γ tape) := by
  change Finite Bool
  infer_instance

end
end MaxCutGames.Explicit.MachineSubdivisionRuntime

namespace MaxCutGames.Explicit.MachineSubdivisionCompose

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionCorrespondence

noncomputable section

variable {α : Type} {q : Nat} {encode : α → List Bool} {f : α → Instance q}

def certifiedOutput (involutive : ∀ a, Involutive (f a)) (a : α) :
    {H : Instance q // Involutive H} := ⟨f a, involutive a⟩

/-- Attach the already-proved property without executing anything or changing
the input or output codec. -/
def certify (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a)) :
    TM2ComputableInPolyTime encode (fun H : {H : Instance q // Involutive H} => gameBits H.val)
      (certifiedOutput involutive) where
  tm := upstream.tm
  inputAlphabet := upstream.inputAlphabet
  outputAlphabet := upstream.outputAlphabet
  time := upstream.time
  outputsFun := upstream.outputsFun

def computableInPolyTime (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a)) :
    TM2ComputableInPolyTime encode gameBits (fun a => SubdivisionTarget.subdivide (f a)) :=
  MachineSequential.composeBits (f := certifiedOutput involutive)
    (g := fun H : {H : Instance q // Involutive H} => SubdivisionTarget.subdivide H.val)
    (certify upstream involutive)
    (MachineSubdivisionRuntime.computableInPolyTime q)

theorem finiteAlphabet (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a))
    (finite : MachineFiniteAlphabet.FiniteAlphabet upstream.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime upstream involutive).tm := by
  exact MachineFiniteAlphabet.composeBits (certify upstream involutive)
    (MachineSubdivisionRuntime.computableInPolyTime q) finite
    (MachineSubdivisionRuntime.workAlphabetFinite q)

/-- Binary-translation producers discharge the only table-law condition. -/
def translationComputableInPolyTime {s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s)
    (upstream : TM2ComputableInPolyTime encode gameBits f)
    (translations : ∀ a, Integration.TranslationTarget.IsTranslationInstance coordinates (f a)) :
    TM2ComputableInPolyTime encode gameBits (fun a => SubdivisionTarget.subdivide (f a)) :=
  computableInPolyTime upstream (fun a => translations_involutive coordinates (f a) (translations a))

end
end MaxCutGames.Explicit.MachineSubdivisionCompose

end OAI
