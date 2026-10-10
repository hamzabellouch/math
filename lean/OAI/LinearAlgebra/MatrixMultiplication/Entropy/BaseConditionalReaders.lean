import OAI.LinearAlgebra.MatrixMultiplication.Tensor.BaseTensorBudgets
import OAI.LinearAlgebra.MatrixMultiplication.Completion.Labels

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.BaseConditionalReaders

open MatrixMultiplication.Foundation CompletionLabels CompletionLabels.TopologicalFlatten
open scoped Classical

universe u

variable {X Y Z : Type u}

def ConditionalLeaf (S : FlaggedTensor X Y Z) (c : Color) :=
  {a : Leaf S // CompletionLabels.leafColor S a = c}

def view (S : FlaggedTensor X Y Z) (c : Color) (k : Color)
    (a : ConditionalLeaf S c) : Coordinate X Y Z k := coordinate a.val.val k

theorem conditional_flag (S : FlaggedTensor X Y Z) (c : Color)
    (a : ConditionalLeaf S c) : ownerFlag S c (coordinate a.val.val c) :=
  (leafColor_eq_iff S a.val c).mp a.property

def trivialSchedule (S : FlaggedTensor X Y Z) (c : Color) :
    TopologicalSchedule (ConditionalLeaf S c) (Coordinate X Y Z) 0 where
  arity := fun _ => 1
  readerPair := fun _ => .xy
  active := fun _ _ => false
  branch := fun _ _ => 0
  view := view S c
  activate := fun _ _ => false
  activate_correct := by intro n hn; omega
  localFirst := fun _ _ => 0
  localSecond := fun _ _ => 0
  localFirst_read := by intro n hn; omega
  localSecond_read := by intro n hn; omega

theorem trivialSchedule_complete (S : FlaggedTensor X Y Z) (c : Color)
    (h : Subsingleton (ConditionalLeaf S c)) :
    (trivialSchedule S c).toNodeSchedule.Complete 0 := by
  intro a b _
  exact h.allEq a b

def binarySchedule {A : Type*} {Coord : Color → Type*}
    (v : (c : Color) → A → Coord c) (pair : ReaderPair)
    (choice : A → Fin 2)
    (first : Coord (firstSide pair) → Fin 2)
    (second : Coord (secondSide pair) → Fin 2)
    (hfirst : ∀ a, first (v (firstSide pair) a) = choice a)
    (hsecond : ∀ a, second (v (secondSide pair) a) = choice a) :
    TopologicalSchedule A Coord 1 where
  arity := fun | 0 => 2 | _ + 1 => 1
  readerPair := fun _ => pair
  active := fun | 0, _ => true | _ + 1, _ => false
  branch := fun | 0, a => choice a | _ + 1, _ => 0
  view := v
  activate := fun | 0, _ => true | _ + 1, _ => false
  activate_correct := by
    intro n hn a
    have hn0 : n = 0 := by omega
    subst n
    rfl
  localFirst := fun | 0, u => first u | _ + 1, _ => 0
  localSecond := fun | 0, u => second u | _ + 1, _ => 0
  localFirst_read := by
    intro n hn a _
    have hn0 : n = 0 := by omega
    subst n
    exact hfirst a
  localSecond_read := by
    intro n hn a _
    have hn0 : n = 0 := by omega
    subst n
    exact hsecond a

theorem binarySchedule_complete {A : Type*} {Coord : Color → Type*}
    (v : (c : Color) → A → Coord c) (pair : ReaderPair)
    (choice : A → Fin 2) (first) (second) (hfirst) (hsecond)
    (hinj : Function.Injective choice) :
    (binarySchedule v pair choice first second hfirst hsecond).toNodeSchedule.Complete 1 := by
  intro a b h
  apply hinj
  exact (h 0 (by omega)).2 rfl

theorem baseTwo_subsingleton (c : Color) :
    Subsingleton (ConditionalLeaf BaseTwo.flagged c) := by
  refine ⟨?_⟩
  intro a b
  have ha := conditional_flag BaseTwo.flagged c a
  have hb := conditional_flag BaseTwo.flagged c b
  have hsa := a.val.property
  have hsb := b.val.property
  apply Subtype.ext
  apply Subtype.ext
  cases c with
  | B =>
      obtain ⟨hax, hay, haz⟩ := (BaseTwo.conditionalB _ _ _).mp ⟨hsa, ha⟩
      obtain ⟨hbx, hby, hbz⟩ := (BaseTwo.conditionalB _ _ _).mp ⟨hsb, hb⟩
      exact Prod.ext (hax.trans hbx.symm) (Prod.ext (hay.trans hby.symm) (haz.trans hbz.symm))
  | A =>
      obtain ⟨hax, hay, haz⟩ := (BaseTwo.conditionalA _ _ _).mp ⟨hsa, ha⟩
      obtain ⟨hbx, hby, hbz⟩ := (BaseTwo.conditionalA _ _ _).mp ⟨hsb, hb⟩
      exact Prod.ext (hax.trans hbx.symm) (Prod.ext (hay.trans hby.symm) (haz.trans hbz.symm))
  | C =>
      obtain ⟨hax, hay, haz⟩ := (BaseTwo.conditionalC _ _ _).mp ⟨hsa, ha⟩
      obtain ⟨hbx, hby, hbz⟩ := (BaseTwo.conditionalC _ _ _).mp ⟨hsb, hb⟩
      exact Prod.ext (hax.trans hbx.symm) (Prod.ext (hay.trans hby.symm) (haz.trans hbz.symm))

def baseTwo (c : Color) :
    TopologicalSchedule (ConditionalLeaf BaseTwo.flagged c)
      (Coordinate (Fin 2) (Fin 2) (Fin 2)) 0 := trivialSchedule BaseTwo.flagged c

theorem baseTwo_complete (c : Color) : (baseTwo c).toNodeSchedule.Complete 0 :=
  trivialSchedule_complete BaseTwo.flagged c (baseTwo_subsingleton c)

def aChoice (a : ConditionalLeaf BaseThree.flagged .A) : Fin 2 :=
  if a.val.val.2.1 = 0 then 0 else 1

def bChoice (a : ConditionalLeaf BaseThree.flagged .B) : Fin 2 :=
  if a.val.val.1 = 2 then 0 else 1

theorem aChoice_read (a : ConditionalLeaf BaseThree.flagged .A) :
    (if a.val.val.2.2 = 2 then (0 : Fin 2) else 1) = aChoice a := by
  have ha := conditional_flag BaseThree.flagged .A a
  have h := BaseThree.readableA _ _ _ a.val.property ha
  simp only [aChoice, ← h]

theorem bChoice_read (a : ConditionalLeaf BaseThree.flagged .B) :
    (if a.val.val.2.1 = 0 then (0 : Fin 2) else 1) = bChoice a := by
  have hb := conditional_flag BaseThree.flagged .B a
  have h := BaseThree.readableB _ _ _ a.val.property hb
  simp only [bChoice, ← h]

theorem aChoice_injective : Function.Injective aChoice := by
  intro a b h
  have ha := (BaseThree.conditionalA _ _ _).mp
    ⟨a.val.property, conditional_flag BaseThree.flagged .A a⟩
  have hb := (BaseThree.conditionalA _ _ _).mp
    ⟨b.val.property, conditional_flag BaseThree.flagged .A b⟩
  rcases ha with ⟨hax, ha | ha⟩ <;> rcases hb with ⟨hbx, hb | hb⟩ <;>
    rcases ha with ⟨hay, haz⟩ <;> rcases hb with ⟨hby, hbz⟩
  all_goals
    first
    | apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (hax.trans hbx.symm) (Prod.ext (hay.trans hby.symm) (haz.trans hbz.symm))
    | simp [aChoice, hay, hby] at h

theorem bChoice_injective : Function.Injective bChoice := by
  intro a b h
  have ha := (BaseThree.conditionalB _ _ _).mp
    ⟨a.val.property, conditional_flag BaseThree.flagged .B a⟩
  have hb := (BaseThree.conditionalB _ _ _).mp
    ⟨b.val.property, conditional_flag BaseThree.flagged .B b⟩
  rcases ha with ⟨haz, ha | ha⟩ <;> rcases hb with ⟨hbz, hb | hb⟩ <;>
    rcases ha with ⟨hax, hay⟩ <;> rcases hb with ⟨hbx, hby⟩
  all_goals
    first
    | apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (hax.trans hbx.symm) (Prod.ext (hay.trans hby.symm) (haz.trans hbz.symm))
    | simp [bChoice, hax, hbx, Fin.ext_iff] at h

def baseThreeA :
    TopologicalSchedule (ConditionalLeaf BaseThree.flagged .A)
      (Coordinate (Fin 3) (Fin 3) (Fin 3)) 1 :=
  binarySchedule (view BaseThree.flagged .A) .yz aChoice
    (fun (y : Fin 3) => if y = 0 then 0 else 1) (fun (z : Fin 3) => if z = 2 then 0 else 1)
    (fun _ => rfl) aChoice_read

def baseThreeB :
    TopologicalSchedule (ConditionalLeaf BaseThree.flagged .B)
      (Coordinate (Fin 3) (Fin 3) (Fin 3)) 1 :=
  binarySchedule (view BaseThree.flagged .B) .xy bChoice
    (fun (x : Fin 3) => if x = 2 then 0 else 1) (fun (y : Fin 3) => if y = 0 then 0 else 1)
    (fun _ => rfl) bChoice_read

theorem baseThreeA_complete : baseThreeA.toNodeSchedule.Complete 1 := by
  unfold baseThreeA
  exact binarySchedule_complete _ _ _ _ _ _ _ aChoice_injective

theorem baseThreeB_complete : baseThreeB.toNodeSchedule.Complete 1 := by
  unfold baseThreeB
  exact binarySchedule_complete _ _ _ _ _ _ _ bChoice_injective

theorem baseThreeC_subsingleton : Subsingleton (ConditionalLeaf BaseThree.flagged .C) := by
  refine ⟨?_⟩
  intro a b
  obtain ⟨hax, hay, haz⟩ := (BaseThree.conditionalC _ _ _).mp
    ⟨a.val.property, conditional_flag BaseThree.flagged .C a⟩
  obtain ⟨hbx, hby, hbz⟩ := (BaseThree.conditionalC _ _ _).mp
    ⟨b.val.property, conditional_flag BaseThree.flagged .C b⟩
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (hax.trans hbx.symm) (Prod.ext (hay.trans hby.symm) (haz.trans hbz.symm))

def baseThreeC :
    TopologicalSchedule (ConditionalLeaf BaseThree.flagged .C)
      (Coordinate (Fin 3) (Fin 3) (Fin 3)) 0 := trivialSchedule BaseThree.flagged .C

theorem baseThreeC_complete : baseThreeC.toNodeSchedule.Complete 0 :=
  trivialSchedule_complete BaseThree.flagged .C baseThreeC_subsingleton

def baseTwoProgram :
    Program (Leaf BaseTwo.flagged) (Coordinate (Fin 2) (Fin 2) (Fin 2))
      Color (Fin 2) 0 where
  context := CompletionLabels.leafColor BaseTwo.flagged
  view := fun side a => coordinate a.val side
  pair := fun _ => .xy
  labels := fun _ _ => 0
  read := fun _ _ _ _ _ => 0
  readable := by intro n hn; omega

theorem baseTwoProgram_complete : baseTwoProgram.Complete := by
  intro a b hc _
  change CompletionLabels.leafColor BaseTwo.flagged a =
    CompletionLabels.leafColor BaseTwo.flagged b at hc
  let aa : ConditionalLeaf BaseTwo.flagged (CompletionLabels.leafColor BaseTwo.flagged a) :=
    ⟨a, rfl⟩
  let bb : ConditionalLeaf BaseTwo.flagged (CompletionLabels.leafColor BaseTwo.flagged a) :=
    ⟨b, hc.symm⟩
  exact congrArg Subtype.val ((baseTwo_subsingleton _).allEq aa bb)

def aLabel (a : Leaf BaseThree.flagged) : Fin 2 :=
  if CompletionLabels.leafColor BaseThree.flagged a = .A then
    if a.val.2.1 = 0 then 0 else 1 else 0

def bLabel (a : Leaf BaseThree.flagged) : Fin 2 :=
  if CompletionLabels.leafColor BaseThree.flagged a = .B then
    if a.val.1 = 2 then 0 else 1 else 0

def aRead (side : Color) (ctx : Color) : Coordinate (Fin 3) (Fin 3) (Fin 3) side → Fin 2 :=
  match side with
  | .B => fun _ => 0
  | .A => fun (z : Fin 3) => if ctx = .A then (if z = 2 then 0 else 1) else 0
  | .C => fun (y : Fin 3) => if ctx = .A then (if y = 0 then 0 else 1) else 0

def bRead (side : Color) (ctx : Color) : Coordinate (Fin 3) (Fin 3) (Fin 3) side → Fin 2 :=
  match side with
  | .B => fun (x : Fin 3) => if ctx = .B then (if x = 2 then 0 else 1) else 0
  | .A => fun _ => 0
  | .C => fun (y : Fin 3) => if ctx = .B then (if y = 0 then 0 else 1) else 0

theorem aRead_correct (a : Leaf BaseThree.flagged) (side : Color)
    (hs : side = firstSide .yz ∨ side = secondSide .yz) :
    aRead side (CompletionLabels.leafColor BaseThree.flagged a) (coordinate a.val side) =
      aLabel a := by
  cases side with
  | B => rcases hs with h | h <;> cases h
  | A =>
      by_cases ha : CompletionLabels.leafColor BaseThree.flagged a = .A
      · have hf := (leafColor_eq_iff BaseThree.flagged a .A).mp ha
        have h := BaseThree.readableA _ _ _ a.property hf
        simp only [aRead, aLabel, ha, ite_true, coordinate, ← h]
      · simp [aRead, aLabel, ha]
  | C => rfl

theorem bRead_correct (a : Leaf BaseThree.flagged) (side : Color)
    (hs : side = firstSide .xy ∨ side = secondSide .xy) :
    bRead side (CompletionLabels.leafColor BaseThree.flagged a) (coordinate a.val side) =
      bLabel a := by
  cases side with
  | B => rfl
  | A => rcases hs with h | h <;> cases h
  | C =>
      by_cases hb : CompletionLabels.leafColor BaseThree.flagged a = .B
      · have hf := (leafColor_eq_iff BaseThree.flagged a .B).mp hb
        have h := BaseThree.readableB _ _ _ a.property hf
        simp only [bRead, bLabel, hb, ite_true, coordinate, ← h]
      · simp [bRead, bLabel, hb]

def baseThreeProgram :
    Program (Leaf BaseThree.flagged) (Coordinate (Fin 3) (Fin 3) (Fin 3))
      Color (Fin 2) 2 where
  context := CompletionLabels.leafColor BaseThree.flagged
  view := fun side a => coordinate a.val side
  pair := fun | 0 => .yz | _ + 1 => .xy
  labels := fun | 0, a => aLabel a | 1, a => bLabel a | _ + 2, _ => 0
  read := fun
    | 0, side, ctx, _, own => aRead side ctx own
    | 1, side, ctx, _, own => bRead side ctx own
    | _ + 2, _, _, _, _ => 0
  readable := by
    intro n hn a side hs
    have hn2 : n = 0 ∨ n = 1 := by omega
    rcases hn2 with rfl | rfl
    · exact aRead_correct a side hs
    · exact bRead_correct a side hs

theorem baseThreeProgram_complete : baseThreeProgram.Complete := by
  intro a b hc hl
  change CompletionLabels.leafColor BaseThree.flagged a =
    CompletionLabels.leafColor BaseThree.flagged b at hc
  cases ha : CompletionLabels.leafColor BaseThree.flagged a with
  | A =>
      have hb : CompletionLabels.leafColor BaseThree.flagged b = .A := hc.symm.trans ha
      let aa : ConditionalLeaf BaseThree.flagged .A := ⟨a, ha⟩
      let bb : ConditionalLeaf BaseThree.flagged .A := ⟨b, hb⟩
      have hh := hl 0 (by omega)
      change aLabel a = aLabel b at hh
      have he : aChoice aa = aChoice bb := by
        simpa only [aLabel, ha, hb, ite_true, aChoice, aa, bb] using hh
      exact congrArg Subtype.val (aChoice_injective he)
  | B =>
      have hb : CompletionLabels.leafColor BaseThree.flagged b = .B := hc.symm.trans ha
      let aa : ConditionalLeaf BaseThree.flagged .B := ⟨a, ha⟩
      let bb : ConditionalLeaf BaseThree.flagged .B := ⟨b, hb⟩
      have hh := hl 1 (by omega)
      change bLabel a = bLabel b at hh
      have he : bChoice aa = bChoice bb := by
        simpa only [bLabel, ha, hb, ite_true, bChoice, aa, bb] using hh
      exact congrArg Subtype.val (bChoice_injective he)
  | C =>
      have hb : CompletionLabels.leafColor BaseThree.flagged b = .C := hc.symm.trans ha
      let aa : ConditionalLeaf BaseThree.flagged .C := ⟨a, ha⟩
      let bb : ConditionalLeaf BaseThree.flagged .C := ⟨b, hb⟩
      exact congrArg Subtype.val (baseThreeC_subsingleton.allEq aa bb)

def baseTwoReadable : ReadableTensor BaseTwo.flagged where
  Code := Fin 2
  depth := 0
  program := baseTwoProgram
  context_eq _ := rfl
  view_eq _ _ := rfl
  complete := baseTwoProgram_complete

def baseThreeReadable : ReadableTensor BaseThree.flagged where
  Code := Fin 2
  depth := 2
  program := baseThreeProgram
  context_eq _ := rfl
  view_eq _ _ := rfl
  complete := baseThreeProgram_complete

end MatrixMultiplication.BaseConditionalReaders

end

end OAI
