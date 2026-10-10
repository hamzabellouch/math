import OAI.LinearAlgebra.MatrixMultiplication.Completion.Scripts
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalLabels

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {X Y Z : Type uCoord}

def Leaf (S : FlaggedTensor X Y Z) :=
  {p : X × Y × Z // S.tensor p.1 p.2.1 p.2.2 ≠ 0}

instance leafFintype [Fintype X] [Fintype Y] [Fintype Z]
    (S : FlaggedTensor X Y Z) : Fintype (Leaf S) :=
  inferInstanceAs (Fintype {p : X × Y × Z // S.tensor p.1 p.2.1 p.2.2 ≠ 0})

def Coordinate (X Y Z : Type uCoord) : Color → Type uCoord
  | .B => X
  | .A => Z
  | .C => Y

def coordinate (p : X × Y × Z) : (c : Color) → Coordinate X Y Z c
  | .B => p.1
  | .A => p.2.2
  | .C => p.2.1

def ownerFlag (S : FlaggedTensor X Y Z) : (c : Color) → Coordinate X Y Z c → Prop
  | .B => S.flagB
  | .A => S.flagA
  | .C => S.flagC

def leafColor (S : FlaggedTensor X Y Z) (a : Leaf S) : Color :=
  if S.flagB a.val.1 then .B else if S.flagA a.val.2.2 then .A else .C

theorem leafColor_eq_iff (S : FlaggedTensor X Y Z) (a : Leaf S) (c : Color) :
    leafColor S a = c ↔ ownerFlag S c (coordinate a.val c) := by
  have h := S.one_hot _ _ _ a.property
  cases c <;>
    by_cases hb : S.flagB a.val.1 <;>
    by_cases ha : S.flagA a.val.2.2 <;>
    by_cases hc : S.flagC a.val.2.1 <;>
    simp_all [leafColor, ownerFlag, coordinate]

theorem complete_supported (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) :
    Tensor.power S.tensor m a.val.1 a.val.2.1 a.val.2.2 ≠ 0 := by
  have h := a.property
  change (if weight S center m a.val.1 a.val.2.1 a.val.2.2 = 1 then
    Tensor.power S.tensor m a.val.1 a.val.2.1 a.val.2.2 else 0) ≠ 0 at h
  split_ifs at h with hw
  · exact h
  · exact False.elim (h rfl)

def slot (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) (i : Fin m) : Leaf S :=
  ⟨(a.val.1 i, a.val.2.1 i, a.val.2.2 i),
    (Finset.prod_ne_zero_iff.mp (complete_supported S center m a)) i (Finset.mem_univ i)⟩

def pattern (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) : Fin m → Color :=
  fun i => leafColor S (slot S center m a i)

theorem slot_injective (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    Function.Injective (slot S center m) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · funext i
    exact congrArg (fun w : Leaf S => w.val.1) (congrFun h i)
  · apply Prod.ext
    · funext i
      exact congrArg (fun w : Leaf S => w.val.2.1) (congrFun h i)
    · funext i
      exact congrArg (fun w : Leaf S => w.val.2.2) (congrFun h i)

theorem completed_color_iff (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) (c : Color) :
    leafColor (complete S center m) a = c ↔
      raisedFlag center c (fun i => pattern S center m a i = c) := by
  rw [leafColor_eq_iff]
  have hold (i : Fin m) := leafColor_eq_iff S (slot S center m a i) c
  have heq : (fun i => pattern S center m a i = c) =
      (fun i => ownerFlag S c (coordinate (slot S center m a i).val c)) := by
    funext i
    exact propext (hold i)
  rw [heq]
  cases c <;> rfl

theorem pattern_mem (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) (i : Fin m) :
    pattern S center m a i = center ∨
      pattern S center m a i = leafColor (complete S center m) a := by
  by_cases hc : pattern S center m a i = center
  · exact Or.inl hc
  · right
    have hn : center ≠ pattern S center m a i := Ne.symm hc
    have hnew : leafColor (complete S center m) a = pattern S center m a i := by
      apply (completed_color_iff S center m a _).mpr
      simp only [raisedFlag, ite_eq_right hn]
      exact ⟨i, rfl⟩
    exact hnew.symm

theorem pattern_eq_center (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m))
    (h : leafColor (complete S center m) a = center) :
    pattern S center m a = fun _ => center := by
  funext i
  have hi := pattern_mem S center m a i
  simpa only [h, or_self] using hi

def centerRead (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (u : Fin m → Coordinate X Y Z center) : Fin m → Color :=
  fun i => if ownerFlag S center (u i) then center else output

def outputRead (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (u : Fin m → Coordinate X Y Z output) : Fin m → Color :=
  fun i => if ownerFlag S output (u i) then output else center

theorem centerRead_pattern (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) :
    centerRead S center (leafColor (complete S center m) a) m
      (fun i => coordinate (slot S center m a i).val center) = pattern S center m a := by
  funext i
  have hc := leafColor_eq_iff S (slot S center m a i) center
  change (if ownerFlag S center _ then center else _) = _
  by_cases h : pattern S center m a i = center
  · rw [ite_eq_left (hc.mp h), h]
  · rw [ite_eq_right (fun hf => h (hc.mpr hf))]
    exact (Or.resolve_left (pattern_mem S center m a i) h).symm

theorem outputRead_pattern (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) :
    outputRead S center (leafColor (complete S center m) a) m
      (fun i => coordinate (slot S center m a i).val
        (leafColor (complete S center m) a)) = pattern S center m a := by
  funext i
  have hc := leafColor_eq_iff S (slot S center m a i)
    (leafColor (complete S center m) a)
  change (if ownerFlag S _ _ then _ else center) = _
  by_cases h : pattern S center m a i = leafColor (complete S center m) a
  · rw [ite_eq_left (hc.mp h), h]
  · rw [ite_eq_right (fun hf => h (hc.mpr hf))]
    exact (Or.resolve_right (pattern_mem S center m a i) h).symm

theorem raisedFlag_iff_output {I : Type*} (p : I → Color) (center output : Color)
    (active : raisedFlag center output (fun i => p i = output))
    (allowed : ∀ i, p i = center ∨ p i = output) (c : Color) :
    raisedFlag center c (fun i => p i = c) ↔ c = output := by
  constructor
  · intro hc
    by_contra hco
    by_cases hcc : center = c
    · subst c
      have hne : center ≠ output := hco
      have ha : ∃ i, p i = output := by
        simpa only [raisedFlag, ite_eq_right hne] using active
      have hall : ∀ i, p i = center := by
        simpa only [raisedFlag, ite_eq_left rfl, ite_true] using hc
      obtain ⟨i, hi⟩ := ha
      exact hne ((hall i).symm.trans hi)
    · have ha : ∃ i, p i = c := by
        simpa only [raisedFlag, ite_eq_right hcc] using hc
      obtain ⟨i, hi⟩ := ha
      rcases allowed i with h | h
      · exact hcc (h.symm.trans hi)
      · exact hco (hi.symm.trans h)
  · rintro rfl
    exact active

def wordCoordinates {m : ℕ} (S : FlaggedTensor X Y Z) (w : Fin m → Leaf S) :
    (Fin m → X) × (Fin m → Y) × (Fin m → Z) :=
  (fun i => (w i).val.1, fun i => (w i).val.2.1, fun i => (w i).val.2.2)

theorem word_ownerFlag (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (w : Fin m → Leaf S) (c : Color) :
    ownerFlag (complete S center m) c (coordinate (wordCoordinates S w) c) ↔
      raisedFlag center c (fun i => leafColor S (w i) = c) := by
  have heq : (fun i => leafColor S (w i) = c) =
      (fun i => ownerFlag S c (coordinate (w i).val c)) := by
    funext i
    exact propext (leafColor_eq_iff S (w i) c)
  rw [heq]
  cases c <;> rfl

def packLeaf (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (w : Fin m → Leaf S)
    (active : raisedFlag center output (fun i => leafColor S (w i) = output))
    (allowed : ∀ i, leafColor S (w i) = center ∨ leafColor S (w i) = output) :
    Leaf (complete S center m) := by
  have hflag (c : Color) :
      ownerFlag (complete S center m) c (coordinate (wordCoordinates S w) c) ↔
        c = output :=
    (word_ownerFlag S center m w c).trans
      (raisedFlag_iff_output _ center output active allowed c)
  have hw : weight S center m (wordCoordinates S w).1
      (wordCoordinates S w).2.1 (wordCoordinates S w).2.2 = 1 := by
    have hb := hflag .B
    have ha := hflag .A
    have hc := hflag .C
    change flagB S center m (wordCoordinates S w).1 ↔ Color.B = output at hb
    change flagA S center m (wordCoordinates S w).2.2 ↔ Color.A = output at ha
    change flagC S center m (wordCoordinates S w).2.1 ↔ Color.C = output at hc
    simp only [weight, hb, ha, hc]
    cases output <;> simp
  refine ⟨wordCoordinates S w, ?_⟩
  rw [complete_tensor, ite_eq_left hw]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (w i).property

@[simp] theorem slot_packLeaf (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (w : Fin m → Leaf S) (active) (allowed) :
    slot S center m (packLeaf S center output m w active allowed) = w := by
  funext i
  apply Subtype.ext
  rfl

theorem packLeaf_color (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (w : Fin m → Leaf S) (active) (allowed) :
    leafColor (complete S center m) (packLeaf S center output m w active allowed) = output := by
  apply (completed_color_iff S center m _ output).mpr
  simpa only [pattern, slot_packLeaf] using active

def conditionalLeafEquiv (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ) :
    {a : Leaf (complete S center m) // leafColor (complete S center m) a = output} ≃
      {w : Fin m → Leaf S //
        raisedFlag center output (fun i => leafColor S (w i) = output) ∧
        ∀ i, leafColor S (w i) = center ∨ leafColor S (w i) = output} where
  toFun a := ⟨slot S center m a.val,
    (completed_color_iff S center m a.val output).mp a.property,
    fun i => by simpa only [pattern, ← a.property] using pattern_mem S center m a.val i⟩
  invFun w := ⟨packLeaf S center output m w.val w.property.1 w.property.2,
    packLeaf_color S center output m w.val w.property.1 w.property.2⟩
  left_inv a := by
    apply Subtype.ext
    apply slot_injective S center m
    simp only [slot_packLeaf]
  right_inv w := by
    apply Subtype.ext
    simp only [slot_packLeaf]

def RetainedLeaf (S : FlaggedTensor X Y Z) (first second : Color) :=
  {a : Leaf S // leafColor S a = first ∨ leafColor S a = second}

instance retainedLeafFintype [Fintype X] [Fintype Y] [Fintype Z]
    (S : FlaggedTensor X Y Z) (first second : Color) :
    Fintype (RetainedLeaf S first second) :=
  inferInstanceAs (Fintype {a : Leaf S // leafColor S a = first ∨ leafColor S a = second})

def terminationFirstRead (S : FlaggedTensor X Y Z) (first second : Color)
    (u : Coordinate X Y Z first) : Color :=
  if ownerFlag S first u then first else second

def terminationSecondRead (S : FlaggedTensor X Y Z) (first second : Color)
    (u : Coordinate X Y Z second) : Color :=
  if ownerFlag S second u then second else first

theorem termination_readable (S : FlaggedTensor X Y Z) (first second : Color)
    (a : RetainedLeaf S first second) :
    terminationFirstRead S first second (coordinate a.val.val first) = leafColor S a.val ∧
    terminationSecondRead S first second (coordinate a.val.val second) = leafColor S a.val := by
  have hf := leafColor_eq_iff S a.val first
  have hs := leafColor_eq_iff S a.val second
  constructor
  · by_cases h : leafColor S a.val = first
    · simp only [terminationFirstRead, ite_eq_left (hf.mp h), h]
    · rw [terminationFirstRead, ite_eq_right (fun hflag => h (hf.mpr hflag))]
      exact (Or.resolve_left a.property h).symm
  · by_cases h : leafColor S a.val = second
    · simp only [terminationSecondRead, ite_eq_left (hs.mp h), h]
    · rw [terminationSecondRead, ite_eq_right (fun hflag => h (hs.mpr hflag))]
      exact (Or.resolve_right a.property h).symm

end MatrixMultiplication.CompletionLabels
namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten

open MatrixMultiplication.Foundation RecursiveCompletion

universe u v

def firstSide : ReaderPair → Color
  | .xy => .B
  | .xz => .B
  | .yz => .C

def secondSide : ReaderPair → Color
  | .xy => .C
  | .xz => .A
  | .yz => .A

structure NodeSchedule (A : Type u) where
  arity : ℕ → ℕ
  readerPair : ℕ → ReaderPair
  active : ℕ → A → Bool
  branch : (n : ℕ) → A → Fin (arity n)

namespace NodeSchedule

variable {A : Type u}

def Label (s : NodeSchedule A) (n : ℕ) : Type := Option (Fin (s.arity n))

instance labelFintype (s : NodeSchedule A) (n : ℕ) : Fintype (s.Label n) :=
  inferInstanceAs (Fintype (Option (Fin (s.arity n))))

def labels (s : NodeSchedule A) (n : ℕ) (a : A) : s.Label n :=
  if s.active n a then some (s.branch n a) else none

@[simp] theorem labels_of_inactive (s : NodeSchedule A) (n : ℕ) (a : A)
    (h : s.active n a = false) : s.labels n a = none := by
  simp [labels, h]; rfl

@[simp] theorem labels_of_active (s : NodeSchedule A) (n : ℕ) (a : A)
    (h : s.active n a = true) : s.labels n a = some (s.branch n a) := by
  simp [labels, h]; rfl

theorem labels_eq_iff (s : NodeSchedule A) (n : ℕ) (a b : A) :
    s.labels n a = s.labels n b ↔
      s.active n a = s.active n b ∧
        (s.active n a = true → s.branch n a = s.branch n b) := by
  cases ha : s.active n a <;> cases hb : s.active n b <;>
    simp [labels, ha, hb]
  · rfl
  · exact ⟨Option.some.inj, congrArg some⟩

def Complete (s : NodeSchedule A) (depth : ℕ) : Prop :=
  ∀ a b, (∀ n, n < depth →
    s.active n a = s.active n b ∧
      (s.active n a = true → s.branch n a = s.branch n b)) → a = b

end NodeSchedule

structure TopologicalSchedule (A : Type u) (Coord : Color → Type v) (depth : ℕ)
    extends NodeSchedule A where
  view : (c : Color) → A → Coord c
  activate : (n : ℕ) → LabelRecord toNodeSchedule.Label n → Bool
  activate_correct : ∀ n, n < depth → ∀ a,
    activate n (labelRecordOf toNodeSchedule.labels n a) = active n a
  localFirst : (n : ℕ) → Coord (firstSide (readerPair n)) → Fin (arity n)
  localSecond : (n : ℕ) → Coord (secondSide (readerPair n)) → Fin (arity n)
  localFirst_read : ∀ n, n < depth → ∀ a, active n a = true →
    localFirst n (view (firstSide (readerPair n)) a) = branch n a
  localSecond_read : ∀ n, n < depth → ∀ a, active n a = true →
    localSecond n (view (secondSide (readerPair n)) a) = branch n a

namespace TopologicalSchedule

variable {A : Type u} {Coord : Color → Type v} {depth : ℕ}

def pairs (s : TopologicalSchedule A Coord depth) : Fin depth → ReaderPair :=
  fun n => s.readerPair n.val

def firstReader (s : TopologicalSchedule A Coord depth) (n : ℕ)
    (prior : LabelRecord s.toNodeSchedule.Label n)
    (own : Coord (firstSide (s.readerPair n))) : s.toNodeSchedule.Label n :=
  if s.activate n prior then some (s.localFirst n own) else none

def secondReader (s : TopologicalSchedule A Coord depth) (n : ℕ)
    (prior : LabelRecord s.toNodeSchedule.Label n)
    (own : Coord (secondSide (s.readerPair n))) : s.toNodeSchedule.Label n :=
  if s.activate n prior then some (s.localSecond n own) else none

theorem firstReader_readable (s : TopologicalSchedule A Coord depth)
    (n : ℕ) (hn : n < depth) (a : A) :
    s.firstReader n (labelRecordOf s.toNodeSchedule.labels n a)
      (s.view (firstSide (s.readerPair n)) a) =
        s.toNodeSchedule.labels n a := by
  simp only [firstReader, NodeSchedule.labels, s.activate_correct n hn a]
  by_cases h : s.active n a = true
  · simp [h, s.localFirst_read n hn a h]; rfl
  · simp [h]; rfl

theorem secondReader_readable (s : TopologicalSchedule A Coord depth)
    (n : ℕ) (hn : n < depth) (a : A) :
    s.secondReader n (labelRecordOf s.toNodeSchedule.labels n a)
      (s.view (secondSide (s.readerPair n)) a) =
        s.toNodeSchedule.labels n a := by
  simp only [secondReader, NodeSchedule.labels, s.activate_correct n hn a]
  by_cases h : s.active n a = true
  · simp [h, s.localSecond_read n hn a h]; rfl
  · simp [h]; rfl

theorem readers_off_branch (s : TopologicalSchedule A Coord depth)
    (n : ℕ) (hn : n < depth) (a : A) (ha : s.active n a = false)
    (ownFirst : Coord (firstSide (s.readerPair n)))
    (ownSecond : Coord (secondSide (s.readerPair n))) :
    s.firstReader n (labelRecordOf s.toNodeSchedule.labels n a) ownFirst = none ∧
      s.secondReader n (labelRecordOf s.toNodeSchedule.labels n a) ownSecond = none := by
  simp [firstReader, secondReader, s.activate_correct n hn a, ha]; rfl

end TopologicalSchedule

theorem labelRecordOf_eq_prefix {A : Type u} {Label : ℕ → Type v}
    (labels : ∀ n, A → Label n) {a b : A} :
    ∀ {m k : ℕ}, k ≤ m →
      labelRecordOf labels m a = labelRecordOf labels m b →
      labelRecordOf labels k a = labelRecordOf labels k b := by
  intro m
  induction m with
  | zero =>
      intro k hk _
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      rfl
  | succ m ih =>
      intro k hk h
      rcases Nat.eq_or_lt_of_le hk with hk | hk
      · subst k
        exact h
      · exact ih (Nat.le_of_lt_succ hk) (congrArg Prod.fst h)

theorem label_eq_of_record_eq {A : Type u} {Label : ℕ → Type v}
    (labels : ∀ n, A → Label n) {depth n : ℕ} {a b : A}
    (h : labelRecordOf labels depth a = labelRecordOf labels depth b)
    (hn : n < depth) : labels n a = labels n b := by
  have hp : labelRecordOf labels (n + 1) a =
      labelRecordOf labels (n + 1) b :=
    labelRecordOf_eq_prefix labels (Nat.succ_le_of_lt hn) h
  exact congrArg Prod.snd hp

namespace NodeSchedule

theorem completeRecord_injective {A : Type u} (s : NodeSchedule A) (depth : ℕ)
    (complete : s.Complete depth) :
    Function.Injective (labelRecordOf s.labels depth) := by
  intro a b h
  apply complete a b
  intro n hn
  exact (s.labels_eq_iff n a b).mp (label_eq_of_record_eq s.labels h hn)

end NodeSchedule

namespace TopologicalSchedule

variable {A : Type u} {Coord : Color → Type v} {depth : ℕ}

theorem completeRecord_injective (s : TopologicalSchedule A Coord depth)
    (complete : s.toNodeSchedule.Complete depth) :
    Function.Injective (labelRecordOf s.toNodeSchedule.labels depth) :=
  s.toNodeSchedule.completeRecord_injective depth complete

end TopologicalSchedule
end MatrixMultiplication.CompletionLabels.TopologicalFlatten

namespace MatrixMultiplication.CompletionLabels

open RecursiveCompletion TopologicalFlatten
attribute [local instance] Classical.propDecidable Classical.decEq

variable {X Y Z : Type uCoord}

def ownerPair : Color → Color → ReaderPair
  | .B, .A | .A, .B => .xz
  | .A, .C | .C, .A => .yz
  | _, _ => .xy

theorem ownerPair_first_mem (center output : Color) (h : center ≠ output) :
    firstSide (ownerPair center output) = center ∨
      firstSide (ownerPair center output) = output := by
  cases center <;> cases output <;> simp_all [ownerPair, firstSide]

theorem ownerPair_second_mem (center output : Color) (h : center ≠ output) :
    secondSide (ownerPair center output) = center ∨
      secondSide (ownerPair center output) = output := by
  cases center <;> cases output <;> simp_all [ownerPair, secondSide]

def patternSideRead (S : FlaggedTensor X Y Z) (center output side : Color) (m : ℕ)
    (u : Fin m → Coordinate X Y Z side) : Fin m → Color :=
  if center = output then fun _ => center
  else if side = center then fun i => if ownerFlag S side (u i) then center else output
  else fun i => if ownerFlag S side (u i) then output else center

theorem patternSideRead_correct (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (a : Leaf (complete S center m))
    (ha : leafColor (complete S center m) a = output) (side : Color)
    (hs : center ≠ output → side = center ∨ side = output) :
    patternSideRead S center output side m
      (fun i => coordinate (slot S center m a i).val side) = pattern S center m a := by
  by_cases h : center = output
  · simp only [patternSideRead, ite_eq_left h]
    exact (pattern_eq_center S center m a (ha.trans h.symm)).symm
  · rcases hs h with heq | heq
    · subst side
      simp only [patternSideRead, ite_eq_right h, ite_true]
      have hr := centerRead_pattern S center m a
      rw [ha] at hr
      unfold centerRead at hr
      exact hr
    · subst side
      simp only [patternSideRead, ite_eq_right h, ite_eq_right (Ne.symm h)]
      have hr := outputRead_pattern S center m a
      rw [ha] at hr
      exact hr

theorem completion_pattern_readers (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (a : Leaf (complete S center m))
    (ha : leafColor (complete S center m) a = output) :
    patternSideRead S center output (firstSide (ownerPair center output)) m
        (fun i => coordinate (slot S center m a i).val (firstSide (ownerPair center output))) =
      pattern S center m a ∧
    patternSideRead S center output (secondSide (ownerPair center output)) m
        (fun i => coordinate (slot S center m a i).val (secondSide (ownerPair center output))) =
      pattern S center m a := by
  exact ⟨patternSideRead_correct S center output m a ha _ (ownerPair_first_mem center output),
    patternSideRead_correct S center output m a ha _ (ownerPair_second_mem center output)⟩

end MatrixMultiplication.CompletionLabels
namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten

open MatrixMultiplication.Foundation RecursiveCompletion

attribute [local instance] Classical.propDecidable Classical.decEq

universe u v w z u' v' w'

namespace NodeSchedule

def PrefixDetermined {A : Type u} (s : NodeSchedule A) (depth : ℕ) : Prop :=
  ∀ n, n < depth → ∀ a b,
    labelRecordOf s.labels n a = labelRecordOf s.labels n b →
      s.active n a = s.active n b

def canonicalActivate {A : Type u} (s : NodeSchedule A) (n : ℕ)
    (prior : LabelRecord s.Label n) : Bool :=
  if h : ∃ a, labelRecordOf s.labels n a = prior then
    s.active n (Classical.choose h)
  else false

theorem canonicalActivate_correct {A : Type u} (s : NodeSchedule A) (depth : ℕ)
    (topological : s.PrefixDetermined depth) (n : ℕ) (hn : n < depth) (a : A) :
    s.canonicalActivate n (labelRecordOf s.labels n a) = s.active n a := by
  unfold canonicalActivate
  split_ifs with h
  · exact topological n hn _ a (Classical.choose_spec h)
  · exact False.elim (h ⟨a, rfl⟩)

end NodeSchedule

namespace TopologicalSchedule

def ofPrefixDetermined {A : Type u} {Coord : Color → Type v} {depth : ℕ}
    (s : NodeSchedule A) (view : (side : Color) → A → Coord side)
    (topological : s.PrefixDetermined depth)
    (localFirst : (n : ℕ) → Coord (firstSide (s.readerPair n)) → Fin (s.arity n))
    (localSecond : (n : ℕ) → Coord (secondSide (s.readerPair n)) → Fin (s.arity n))
    (first_correct : ∀ n, n < depth → ∀ a, s.active n a = true →
      localFirst n (view (firstSide (s.readerPair n)) a) = s.branch n a)
    (second_correct : ∀ n, n < depth → ∀ a, s.active n a = true →
      localSecond n (view (secondSide (s.readerPair n)) a) = s.branch n a) :
    TopologicalSchedule A Coord depth where
  toNodeSchedule := s
  view := view
  activate := s.canonicalActivate
  activate_correct := s.canonicalActivate_correct depth topological
  localFirst := localFirst
  localSecond := localSecond
  localFirst_read := first_correct
  localSecond_read := second_correct

end TopologicalSchedule

structure Program (A : Type u) (Coord : Color → Type v)
    (Context : Type z) (Code : Type w) (depth : ℕ) where
  context : A → Context
  view : (side : Color) → A → Coord side
  pair : ℕ → ReaderPair
  labels : ℕ → A → Code
  read : (n : ℕ) → (side : Color) → Context → (Fin n → Code) → Coord side → Code
  readable : ∀ n, n < depth → ∀ a side,
    (side = firstSide (pair n) ∨ side = secondSide (pair n)) →
      read n side (context a) (fun j => labels j.val a) (view side a) = labels n a

namespace Program

variable {A : Type u} {Coord : Color → Type v}
  {Context : Type z} {Code : Type w} {depth : ℕ}

def Complete (p : Program A Coord Context Code depth) : Prop :=
  ∀ a b, p.context a = p.context b →
    (∀ n, n < depth → p.labels n a = p.labels n b) → a = b

def pullback {B : Type u'} {NewCoord : Color → Type v'}
    (p : Program A Coord Context Code depth) (source : B → A)
    (view : (side : Color) → B → NewCoord side)
    (project : (side : Color) → NewCoord side → Coord side)
    (projects : ∀ side b, project side (view side b) = p.view side (source b)) :
    Program B NewCoord Context Code depth where
  context b := p.context (source b)
  view := view
  pair := p.pair
  labels n b := p.labels n (source b)
  read n side ctx prior own := p.read n side ctx prior (project side own)
  readable := by
    intro n hn b side hs
    simpa only [projects side b] using p.readable n hn (source b) side hs

theorem pullback_complete {B : Type u'} {NewCoord : Color → Type v'}
    (p : Program A Coord Context Code depth) (source : B → A)
    (view : (side : Color) → B → NewCoord side)
    (project : (side : Color) → NewCoord side → Coord side)
    (projects : ∀ side b, project side (view side b) = p.view side (source b))
    (complete : p.Complete) (injective : Function.Injective source) :
    (p.pullback source view project projects).Complete := by
  intro a b hc hl
  apply injective
  exact complete (source a) (source b) hc hl

def recode {NewCode : Type w'} (p : Program A Coord Context Code depth)
    (encode : Code → NewCode) (decode : NewCode → Code)
    (roundtrip : Function.LeftInverse decode encode) :
    Program A Coord Context NewCode depth where
  context := p.context
  view := p.view
  pair := p.pair
  labels n a := encode (p.labels n a)
  read n side ctx prior own := encode (p.read n side ctx (fun j => decode (prior j)) own)
  readable := by
    intro n hn a side hs
    have hprior : (fun j : Fin n => decode (encode (p.labels j.val a))) =
        (fun j : Fin n => p.labels j.val a) := by
      funext j
      exact roundtrip _
    dsimp
    rw [hprior, p.readable n hn a side hs]

theorem recode_complete {NewCode : Type w'} (p : Program A Coord Context Code depth)
    (encode : Code → NewCode) (decode : NewCode → Code)
    (roundtrip : Function.LeftInverse decode encode) (complete : p.Complete) :
    (p.recode encode decode roundtrip).Complete := by
  intro a b hc hl
  apply complete a b hc
  intro n hn
  exact roundtrip.injective (hl n hn)

def single (context : A → Context) (view : (side : Color) → A → Coord side)
    (pair : ReaderPair) (label : A → Code)
    (read : (side : Color) → Context → Coord side → Code)
    (correct : ∀ a side, (side = firstSide pair ∨ side = secondSide pair) →
      read side (context a) (view side a) = label a) :
    Program A Coord Context Code 1 where
  context := context
  view := view
  pair _ := pair
  labels _ := label
  read _ side ctx _ own := read side ctx own
  readable := by
    intro n hn a side hs
    exact correct a side hs

private def appendLabel (d : ℕ) (f g : ℕ → A → Code) (n : ℕ) (a : A) : Code :=
  if n < d then f n a else g (n - d) a

private def takeArray {n d : ℕ} (h : d ≤ n) (prior : Fin n → Code) : Fin d → Code :=
  fun j => prior ⟨j.val, lt_of_lt_of_le j.isLt h⟩

private def dropArray {n d : ℕ} (h : d ≤ n) (prior : Fin n → Code) : Fin (n - d) → Code :=
  fun j => prior ⟨d + j.val, by omega⟩

def append {OtherContext : Type z} {d e : ℕ}
    (p : Program A Coord Context Code d) (q : Program A Coord OtherContext Code e)
    (sameView : ∀ side a, p.view side a = q.view side a)
    (derive : Context → (Fin d → Code) → OtherContext)
    (derive_correct : ∀ a, derive (p.context a) (fun j => p.labels j.val a) = q.context a) :
    Program A Coord Context Code (d + e) where
  context := p.context
  view := p.view
  pair n := if n < d then p.pair n else q.pair (n - d)
  labels := appendLabel d p.labels q.labels
  read n side ctx prior own :=
    if h : n < d then p.read n side ctx prior own
    else q.read (n - d) side
      (derive ctx (takeArray (Nat.le_of_not_gt h) prior))
      (dropArray (Nat.le_of_not_gt h) prior) own
  readable := by
    intro n hn a side hs
    by_cases h : n < d
    · have hprior : (fun j : Fin n => appendLabel d p.labels q.labels j.val a) =
          (fun j : Fin n => p.labels j.val a) := by
        funext j
        simp [appendLabel, lt_trans j.isLt h]
      simp only [ite_eq_left h] at hs
      simp only [dite_eq_left h]
      rw [hprior]
      simpa only [appendLabel, ite_eq_left h] using p.readable n h a side hs
    · have hd : d ≤ n := Nat.le_of_not_gt h
      have hhead : takeArray hd (fun j : Fin n => appendLabel d p.labels q.labels j.val a) =
          (fun j : Fin d => p.labels j.val a) := by
        funext j
        simp [takeArray, appendLabel, j.isLt]
      have htail : dropArray hd (fun j : Fin n => appendLabel d p.labels q.labels j.val a) =
          (fun j : Fin (n - d) => q.labels j.val a) := by
        funext j
        have hj : ¬ d + j.val < d := by omega
        simp [dropArray, appendLabel, hj]
      have hnq : n - d < e := by omega
      simp only [ite_eq_right h] at hs
      simp only [dite_eq_right h]
      rw [hhead, htail, derive_correct a, sameView side a]
      simpa only [appendLabel, ite_eq_right h] using q.readable (n - d) hnq a side hs

theorem append_labels_left {OtherContext : Type z} {d e : ℕ}
    (p : Program A Coord Context Code d) (q : Program A Coord OtherContext Code e)
    (sameView : ∀ side a, p.view side a = q.view side a)
    (derive : Context → (Fin d → Code) → OtherContext)
    (derive_correct : ∀ a, derive (p.context a) (fun j => p.labels j.val a) = q.context a)
    (n : ℕ) (hn : n < d) (a : A) :
    (p.append q sameView derive derive_correct).labels n a = p.labels n a := by
  simp [append, appendLabel, hn]

theorem append_labels_right {OtherContext : Type z} {d e : ℕ}
    (p : Program A Coord Context Code d) (q : Program A Coord OtherContext Code e)
    (sameView : ∀ side a, p.view side a = q.view side a)
    (derive : Context → (Fin d → Code) → OtherContext)
    (derive_correct : ∀ a, derive (p.context a) (fun j => p.labels j.val a) = q.context a)
    (n : ℕ) (a : A) :
    (p.append q sameView derive derive_correct).labels (d + n) a = q.labels n a := by
  have h : ¬d + n < d := by omega
  simp [append, appendLabel, h]

theorem append_complete {OtherContext : Type z} {d e : ℕ}
    (p : Program A Coord Context Code d) (q : Program A Coord OtherContext Code e)
    (sameView : ∀ side a, p.view side a = q.view side a)
    (derive : Context → (Fin d → Code) → OtherContext)
    (derive_correct : ∀ a, derive (p.context a) (fun j => p.labels j.val a) = q.context a)
    (complete : q.Complete) :
    (p.append q sameView derive derive_correct).Complete := by
  intro a b hc hl
  change p.context a = p.context b at hc
  have hhead : (fun j : Fin d => p.labels j.val a) =
      (fun j : Fin d => p.labels j.val b) := by
    funext j
    have h := hl j.val (by omega)
    simpa only [append_labels_left p q sameView derive derive_correct j.val j.isLt] using h
  have hctx : q.context a = q.context b := by
    rw [← derive_correct a, ← derive_correct b, hc, hhead]
  apply complete a b hctx
  intro n hn
  have h := hl (d + n) (by omega)
  simpa only [append_labels_right] using h

def recordArray {Code : Type w} :
    (n : ℕ) → LabelRecord (fun _ => Code) n → Fin n → Code
  | 0, _, i => Fin.elim0 i
  | n + 1, prior, i =>
      if h : i.val < n then recordArray n prior.1 ⟨i.val, h⟩ else prior.2

theorem recordArray_labelRecordOf {B : Type u'} (labels : ℕ → B → Code)
    (n : ℕ) (a : B) :
    recordArray n (labelRecordOf labels n a) = (fun i => labels i.val a) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      funext i
      by_cases h : i.val < n
      · simp only [recordArray, dite_eq_left h]
        exact congrFun ih ⟨i.val, h⟩
      · have hi : i.val = n := by omega
        simp [recordArray, hi, labelRecordOf]

def firstReader (p : Program A Coord Context Code depth) (n : ℕ) (ctx : Context)
    (prior : LabelRecord (fun _ => Code) n)
    (own : Coord (firstSide (p.pair n))) : Code :=
  p.read n (firstSide (p.pair n)) ctx (recordArray n prior) own

def secondReader (p : Program A Coord Context Code depth) (n : ℕ) (ctx : Context)
    (prior : LabelRecord (fun _ => Code) n)
    (own : Coord (secondSide (p.pair n))) : Code :=
  p.read n (secondSide (p.pair n)) ctx (recordArray n prior) own

theorem firstReader_readable (p : Program A Coord Context Code depth)
    (n : ℕ) (hn : n < depth) (a : A) :
    p.firstReader n (p.context a) (labelRecordOf p.labels n a)
      (p.view (firstSide (p.pair n)) a) = p.labels n a := by
  rw [firstReader, recordArray_labelRecordOf]
  exact p.readable n hn a _ (Or.inl rfl)

theorem secondReader_readable (p : Program A Coord Context Code depth)
    (n : ℕ) (hn : n < depth) (a : A) :
    p.secondReader n (p.context a) (labelRecordOf p.labels n a)
      (p.view (secondSide (p.pair n)) a) = p.labels n a := by
  rw [secondReader, recordArray_labelRecordOf]
  exact p.readable n hn a _ (Or.inr rfl)

theorem record_injective_on_context (p : Program A Coord Context Code depth)
    (complete : p.Complete) (ctx : Context) :
    Function.Injective
      (fun a : {a : A // p.context a = ctx} => labelRecordOf p.labels depth a.val) := by
  intro a b h
  apply Subtype.ext
  apply complete a.val b.val (a.property.trans b.property.symm)
  intro n hn
  exact label_eq_of_record_eq p.labels h hn

end Program
end MatrixMultiplication.CompletionLabels.TopologicalFlatten

namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion TopologicalFlatten
attribute [local instance] Classical.propDecidable Classical.decEq

variable {X Y Z : Type uCoord}

def rootColor (n : ℕ) : Color := if n = 0 then .B else if n = 1 then .A else .C

def rootIndex : Color → Fin 3
  | .B => 0
  | .A => 1
  | .C => 2

@[simp] theorem rootColor_rootIndex (c : Color) : rootColor (rootIndex c).val = c := by
  cases c <;> simp [rootIndex, rootColor]

def completionView (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (side : Color) (a : Leaf (complete S center m)) : Fin m → Coordinate X Y Z side :=
  fun i => coordinate (slot S center m a i).val side

def patternProgram (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    Program (Leaf (complete S center m)) (fun side => Fin m → Coordinate X Y Z side)
      Color (Option (Fin m → Color)) 3 where
  context := leafColor (complete S center m)
  view := completionView S center m
  pair n := ownerPair center (rootColor n)
  labels n a := if leafColor (complete S center m) a = rootColor n then
    some (pattern S center m a) else none
  read n side ctx _ own := if ctx = rootColor n then
    some (patternSideRead S center ctx side m own) else none
  readable := by
    intro n hn a side hs
    by_cases h : leafColor (complete S center m) a = rootColor n
    · simp only [ite_eq_left h]
      congr 1
      apply patternSideRead_correct S center _ m a rfl side
      intro hne
      have hmem : side = center ∨ side = rootColor n := by
        rcases hs with rfl | rfl
        · exact ownerPair_first_mem center (rootColor n) (by simpa only [h] using hne)
        · exact ownerPair_second_mem center (rootColor n) (by simpa only [h] using hne)
      simpa only [h] using hmem
    · simp only [ite_eq_right h]

def decodePattern (center : Color) (m : ℕ) (output : Color)
    (prior : Fin 3 → Option (Fin m → Color)) : Fin m → Color :=
  (prior (rootIndex output)).getD (fun _ => center)

theorem decodePattern_correct (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) :
    decodePattern center m ((patternProgram S center m).context a)
      (fun j => (patternProgram S center m).labels j.val a) = pattern S center m a := by
  simp [decodePattern, patternProgram]

end MatrixMultiplication.CompletionLabels
namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program

open MatrixMultiplication.Foundation RecursiveCompletion

universe u v w z

variable {A : Type u} {Coord : Color → Type v}
  {Context : Type z} {Code : Type w} {depth : ℕ}

private def powPast (d n : ℕ) (j : Fin (n % d)) : Fin n :=
  ⟨(n / d) * d + j.val, by
    calc
      (n / d) * d + j.val < (n / d) * d + n % d :=
        Nat.add_lt_add_left j.isLt _
      _ = n := by
        simpa only [Nat.mul_comm] using Nat.div_add_mod n d⟩

private def powLabel [Inhabited Code]
    (p : Program A Coord Context Code depth) (m n : ℕ) (a : Fin m → A) : Code :=
  if hi : n / depth < m then
    p.labels (n % depth) (a ⟨n / depth, hi⟩)
  else default

private theorem powLabel_at [Inhabited Code]
    (p : Program A Coord Context Code depth) (m : ℕ)
    (a : Fin m → A) (i : Fin m) {k : ℕ} (hk : k < depth) :
    powLabel p m (i.val * depth + k) a = p.labels k (a i) := by
  have hd : 0 < depth := lt_of_le_of_lt (Nat.zero_le k) hk
  have hquot : (i.val * depth + k) / depth = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd,
      Nat.div_eq_of_lt hk, Nat.zero_add]
  have hrem : (i.val * depth + k) % depth = k := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hk]
  simp only [powLabel, hquot, hrem, dite_eq_left i.isLt]

def pow [Inhabited Code] (p : Program A Coord Context Code depth) (m : ℕ) :
    Program (Fin m → A) (fun side => Fin m → Coord side)
      (Fin m → Context) Code (m * depth) where
  context a i := p.context (a i)
  view side a i := p.view side (a i)
  pair n := p.pair (n % depth)
  labels := powLabel p m
  read n side ctx prior own :=
    if hi : n / depth < m then
      p.read (n % depth) side (ctx ⟨n / depth, hi⟩)
        (fun j => prior (powPast depth n j)) (own ⟨n / depth, hi⟩)
    else default
  readable := by
    intro n hn a side hs
    have hd : 0 < depth := by
      by_contra h
      have hzero : depth = 0 := by omega
      simp [hzero] at hn
    have hi : n / depth < m := (Nat.div_lt_iff_lt_mul hd).2 hn
    let i : Fin m := ⟨n / depth, hi⟩
    have hlocal : n % depth < depth := Nat.mod_lt n hd
    have hprior :
        (fun j : Fin (n % depth) => powLabel p m (powPast depth n j).val a) =
        (fun j : Fin (n % depth) => p.labels j.val (a i)) := by
      funext j
      change powLabel p m (i.val * depth + j.val) a = p.labels j.val (a i)
      exact powLabel_at p m a i (lt_trans j.isLt hlocal)
    simp only [dite_eq_left hi]
    change p.read (n % depth) side (p.context (a i))
      (fun j : Fin (n % depth) => powLabel p m (powPast depth n j).val a)
      (p.view side (a i)) = powLabel p m n a
    rw [hprior]
    simpa only [powLabel, dite_eq_left hi] using
      p.readable (n % depth) hlocal (a i) side hs

theorem pow_labels [Inhabited Code] (p : Program A Coord Context Code depth) (m : ℕ)
    (a : Fin m → A) (i : Fin m) (n : ℕ) (hn : n < depth) :
    (p.pow m).labels (i.val * depth + n) a = p.labels n (a i) :=
  powLabel_at p m a i hn

theorem pow_complete [Inhabited Code]
    (p : Program A Coord Context Code depth) (m : ℕ) (complete : p.Complete) :
    (p.pow m).Complete := by
  intro a b hc hl
  funext i
  apply complete (a i) (b i)
  · exact congrFun hc i
  · intro k hk
    have hindex : i.val * depth + k < m * depth := by
      calc
        i.val * depth + k < i.val * depth + depth := Nat.add_lt_add_left hk _
        _ = (i.val + 1) * depth := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ m * depth := Nat.mul_le_mul_right depth (Nat.succ_le_of_lt i.isLt)
    have h := hl (i.val * depth + k) hindex
    change powLabel p m (i.val * depth + k) a =
      powLabel p m (i.val * depth + k) b at h
    rw [powLabel_at p m a i hk, powLabel_at p m b i hk] at h
    exact h

end MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program

namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion TopologicalFlatten

universe w
variable {X Y Z : Type uCoord} {Code : Type w} {depth : ℕ}

abbrev CompletionCode (m : ℕ) (Code : Type w) := Option ((Fin m → Color) ⊕ Code)

def encodePattern {m : ℕ} : Option (Fin m → Color) → CompletionCode m Code
  | none => none
  | some pattern => some (.inl pattern)

def decodePatternCode {m : ℕ} : CompletionCode m Code → Option (Fin m → Color)
  | some (.inl pattern) => some pattern
  | _ => none

theorem patternCode_roundtrip {m : ℕ} :
    Function.LeftInverse (decodePatternCode (Code := Code)) (encodePattern (m := m)) := by
  intro c
  cases c <;> rfl

def encodeOld {m : ℕ} (c : Code) : CompletionCode m Code := some (.inr c)

def decodeOld [Inhabited Code] {m : ℕ} : CompletionCode m Code → Code
  | some (.inr c) => c
  | _ => default

theorem oldCode_roundtrip [Inhabited Code] {m : ℕ} :
    Function.LeftInverse (decodeOld (Code := Code) (m := m)) encodeOld := by
  intro c
  rfl

def inheritedProgram (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side) :
    Program (Leaf (complete S center m)) (fun side => Fin m → Coordinate X Y Z side)
      (Fin m → Color) (CompletionCode m Code) (m * depth) :=
  let old := p.recode encodeOld decodeOld oldCode_roundtrip
  (old.pow m).pullback (slot S center m) (completionView S center m)
    (fun _ => id) (by
      intro side a
      funext i
      exact (view_eq side (slot S center m a i)).symm)

theorem inheritedProgram_complete (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (complete : p.Complete) :
    (inheritedProgram S center m p view_eq).Complete := by
  exact Program.pullback_complete
    ((p.recode encodeOld decodeOld oldCode_roundtrip).pow m)
    (slot S center m) (completionView S center m) (fun _ => id)
    (by intro side a; funext i; exact (view_eq side (slot S center m a i)).symm)
    (Program.pow_complete _ m
      (Program.recode_complete p encodeOld decodeOld oldCode_roundtrip complete))
    (slot_injective S center m)

private def completionContextDecoder (center : Color) (m : ℕ) (output : Color)
    (prior : Fin 3 → CompletionCode m Code) : Fin m → Color :=
  decodePattern center m output (fun i => decodePatternCode (prior i))

private theorem completionContextDecoder_correct
    (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (a : Leaf (complete S center m)) :
    completionContextDecoder (Code := Code) center m
      (((patternProgram S center m).recode (encodePattern (Code := Code)) decodePatternCode
        patternCode_roundtrip).context a)
      (fun j => ((patternProgram S center m).recode (encodePattern (Code := Code)) decodePatternCode
        patternCode_roundtrip).labels j.val a) =
      (inheritedProgram S center m p view_eq).context a := by
  change decodePattern center m (leafColor (complete S center m) a)
    (fun j => decodePatternCode (Code := Code)
      (encodePattern ((patternProgram S center m).labels j.val a))) =
      (fun i => p.context (slot S center m a i))
  have hr (c : Option (Fin m → Color)) :
      decodePatternCode (encodePattern c : CompletionCode m Code) = c := patternCode_roundtrip c
  simp only [hr]
  exact (decodePattern_correct S center m a).trans (by
    funext i
    exact (context_eq (slot S center m a i)).symm)

def completionProgram (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side) :
    Program (Leaf (complete S center m)) (fun side => Fin m → Coordinate X Y Z side)
      Color (CompletionCode m Code) (3 + m * depth) :=
  ((patternProgram S center m).recode encodePattern decodePatternCode patternCode_roundtrip).append
    (inheritedProgram S center m p view_eq) (fun _ _ => rfl)
    (completionContextDecoder center m)
    (completionContextDecoder_correct S center m p context_eq view_eq)

theorem completionProgram_complete (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (complete : p.Complete) :
    (completionProgram S center m p context_eq view_eq).Complete := by
  exact Program.append_complete
    ((patternProgram S center m).recode encodePattern decodePatternCode patternCode_roundtrip)
    (inheritedProgram S center m p view_eq) (fun _ _ => rfl)
    (completionContextDecoder center m)
    (completionContextDecoder_correct S center m p context_eq view_eq)
    (inheritedProgram_complete S center m p view_eq complete)

def coordinateWord (m : ℕ) (side : Color) :
    Coordinate (Fin m → X) (Fin m → Y) (Fin m → Z) side →
      (Fin m → Coordinate X Y Z side) := by
  cases side <;> exact id

theorem coordinateWord_coordinate (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (side : Color) (a : Leaf (complete S center m)) :
    coordinateWord m side (coordinate a.val side) = completionView S center m side a := by
  cases side <;> rfl

def completionLocalProgram (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side) :
    Program (Leaf (complete S center m))
      (Coordinate (Fin m → X) (Fin m → Y) (Fin m → Z))
      Color (CompletionCode m Code) (3 + m * depth) :=
  (completionProgram S center m p context_eq view_eq).pullback id
    (fun side a => coordinate a.val side) (coordinateWord m)
    (coordinateWord_coordinate S center m)

theorem completionLocalProgram_complete (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (complete : p.Complete) :
    (completionLocalProgram S center m p context_eq view_eq).Complete := by
  exact Program.pullback_complete (completionProgram S center m p context_eq view_eq)
    id (fun side a => coordinate a.val side) (coordinateWord m)
    (coordinateWord_coordinate S center m)
    (completionProgram_complete S center m p context_eq view_eq complete)
    Function.injective_id

structure ReadableTensor (S : FlaggedTensor X Y Z) where
  Code : Type
  [finiteCode : Fintype Code]
  [inhabitedCode : Inhabited Code]
  depth : ℕ
  program : Program (Leaf S) (Coordinate X Y Z) Color Code depth
  context_eq : ∀ a, program.context a = leafColor S a
  view_eq : ∀ side a, program.view side a = coordinate a.val side
  complete : program.Complete

attribute [instance] ReadableTensor.finiteCode ReadableTensor.inhabitedCode

namespace ReadableTensor

def raise (S : FlaggedTensor X Y Z) (r : ReadableTensor S) (center : Color) (m : ℕ) :
    ReadableTensor (RecursiveCompletion.complete S center m) where
  Code := CompletionCode m r.Code
  depth := 3 + m * r.depth
  program := completionLocalProgram S center m r.program r.context_eq r.view_eq
  context_eq _ := rfl
  view_eq _ _ := rfl
  complete := completionLocalProgram_complete S center m r.program r.context_eq r.view_eq r.complete

def script (S : FlaggedTensor X Y Z) (r : ReadableTensor S) :
    (s : Script) → ReadableTensor (Script.tensor S s)
  | .base => r
  | .step prior center m => raise _ (script S r prior) center m

end ReadableTensor

end MatrixMultiplication.CompletionLabels
namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion TopologicalFlatten

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {X Y Z : Type uCoord} {Code : Type u} {depth : ℕ}

def terminationSideRead (S : FlaggedTensor X Y Z) (first second side : Color)
    (own : Coordinate X Y Z side) : Color :=
  if side = first then
    if ownerFlag S side own then first else second
  else if ownerFlag S side own then second else first

theorem terminationSideRead_correct (S : FlaggedTensor X Y Z)
    (first second : Color) (distinct : first ≠ second)
    (a : RetainedLeaf S first second) (side : Color)
    (hs : side = first ∨ side = second) :
    terminationSideRead S first second side (coordinate a.val.val side) =
      leafColor S a.val := by
  rcases hs with h | h
  · subst side
    simpa only [terminationSideRead, ite_eq_left rfl, ite_true, terminationFirstRead] using
      (termination_readable S first second a).1
  · subst side
    simpa only [terminationSideRead, ite_eq_right (Ne.symm distinct), terminationSecondRead] using
      (termination_readable S first second a).2

def terminationRoot (S : FlaggedTensor X Y Z) (first second : Color)
    (distinct : first ≠ second) :
    Program (RetainedLeaf S first second) (Coordinate X Y Z) PUnit Color 1 :=
  Program.single (fun _ => PUnit.unit)
    (fun side a => coordinate a.val.val side)
    (ownerPair first second) (fun a => leafColor S a.val)
    (fun side _ own => terminationSideRead S first second side own)
    (by
      intro a side hs
      apply terminationSideRead_correct S first second distinct a side
      rcases hs with h | h
      · rw [h]
        exact ownerPair_first_mem first second distinct
      · rw [h]
        exact ownerPair_second_mem first second distinct)

def terminationInherited (S : FlaggedTensor X Y Z) (first second : Color)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side) :
    Program (RetainedLeaf S first second) (Coordinate X Y Z) Color Code depth :=
  p.pullback Subtype.val (fun side a => coordinate a.val.val side) (fun _ => id)
    (fun side a => (view_eq side a.val).symm)

theorem terminationInherited_complete (S : FlaggedTensor X Y Z) (first second : Color)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (complete : p.Complete) :
    (terminationInherited S first second p view_eq).Complete := by
  unfold terminationInherited
  exact p.pullback_complete
    (fun a : RetainedLeaf S first second => a.val)
    (fun side a => coordinate a.val.val side) (fun _ => id)
    (fun side a => (view_eq side a.val).symm) complete Subtype.val_injective

def terminationDecodeColor (fallback : Color) : Color ⊕ Code → Color
  | .inl color => color
  | .inr _ => fallback

def terminationDecodeOld [Inhabited Code] : Color ⊕ Code → Code
  | .inl _ => default
  | .inr code => code

def terminationProgram [Inhabited Code]
    (S : FlaggedTensor X Y Z) (first second : Color) (distinct : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side) :
    Program (RetainedLeaf S first second) (Coordinate X Y Z)
      PUnit (Color ⊕ Code) (1 + depth) :=
  ((terminationRoot S first second distinct).recode Sum.inl
    (terminationDecodeColor first) (fun _ => rfl)).append
    ((terminationInherited S first second p view_eq).recode Sum.inr
      terminationDecodeOld (fun _ => rfl))
    (by intro side a; rfl)
    (fun _ prior => terminationDecodeColor first (prior 0))
    (by
      intro a
      change leafColor S a.val = p.context a.val
      exact (context_eq a.val).symm)

theorem terminationProgram_complete [Inhabited Code]
    (S : FlaggedTensor X Y Z) (first second : Color) (distinct : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (complete : p.Complete) :
    (terminationProgram S first second distinct p context_eq view_eq).Complete := by
  exact Program.append_complete
    ((terminationRoot S first second distinct).recode Sum.inl
      (terminationDecodeColor first) (fun _ => rfl))
    ((terminationInherited S first second p view_eq).recode Sum.inr
      terminationDecodeOld (fun _ => rfl))
    (by intro side a; rfl)
    (fun _ prior => terminationDecodeColor first (prior 0))
    (by
      intro a
      change leafColor S a.val = p.context a.val
      exact (context_eq a.val).symm)
    (Program.recode_complete (terminationInherited S first second p view_eq)
      Sum.inr terminationDecodeOld (fun _ => rfl)
      (terminationInherited_complete S first second p view_eq complete))

@[simp] theorem terminationProgram_context [Inhabited Code]
    (S : FlaggedTensor X Y Z) (first second : Color) (distinct : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (a : RetainedLeaf S first second) :
    (terminationProgram S first second distinct p context_eq view_eq).context a =
      PUnit.unit := rfl

@[simp] theorem terminationProgram_view [Inhabited Code]
    (S : FlaggedTensor X Y Z) (first second : Color) (distinct : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (side : Color) (a : RetainedLeaf S first second) :
    (terminationProgram S first second distinct p context_eq view_eq).view side a =
      coordinate a.val.val side := rfl

theorem terminationRecord_injective [Inhabited Code]
    (S : FlaggedTensor X Y Z) (first second : Color) (distinct : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (complete : p.Complete) :
    Function.Injective (labelRecordOf
      (terminationProgram S first second distinct p context_eq view_eq).labels (1 + depth)) := by
  intro a b h
  apply terminationProgram_complete S first second distinct p context_eq view_eq complete a b rfl
  intro n hn
  exact label_eq_of_record_eq _ h hn

end MatrixMultiplication.CompletionLabels

end

end OAI
