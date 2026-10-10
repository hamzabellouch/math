import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.ComplexCW75Primitive
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchyEntropy

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation.CW75LabelHierarchy

open Elementary
open scoped Classical

abbrev Word := CW75Primitive.Word
abbrev BitWord := Fin 3 → Bool

def retainedWords : Finset (List BoundaryTerm) :=
  (Elementary.triples.filter Elementary.retained).toFinset

abbrev Scalar := ↥retainedWords

theorem scalar_mem (a : Scalar) :
    a.val ∈ Elementary.triples.filter Elementary.retained := by
  exact List.mem_toFinset.mp a.property

theorem scalar_card : Fintype.card Scalar = 75 := by
  rw [Fintype.card_coe, retainedWords,
    List.toFinset_card_of_nodup (CW75Primitive.triples_nodup.filter _)]
  exact Elementary.retained_triples_count

def letter (a : Scalar) (i : Fin 3) : BoundaryTerm := a.val.getD i.val .a0

def grade (a : Scalar) : Fin 3 → CWOriginalWords.OriginalComponent :=
  fun i => CW75Primitive.component (letter a i)

def x (a : Scalar) : Word := CWOriginalWords.xWord (grade a)
def y (a : Scalar) : Word := CWOriginalWords.yWord (grade a)
def z (a : Scalar) : Word := CWOriginalWords.zWord (grade a)

theorem coefficient_one (a : Scalar) : CW75Primitive.tensor (x a) (y a) (z a) = 1 :=
  CW75Primitive.retained_coefficient_one a.val (scalar_mem a)

theorem coefficient_ne_zero (a : Scalar) :
    CW75Primitive.tensor (x a) (y a) (z a) ≠ 0 := by
  rw [coefficient_one]
  exact one_ne_zero

theorem grade_injective : Function.Injective grade := by
  intro a b h
  apply Subtype.ext
  exact CW75Primitive.listedWords_injective a.val b.val
    (List.mem_filter.mp (scalar_mem a)).1 (List.mem_filter.mp (scalar_mem b)).1
    (congrArg CWOriginalWords.originalWords h)

theorem coordinates_injective : Function.Injective (fun a : Scalar => (x a, y a, z a)) := by
  intro a b h
  apply grade_injective
  exact CWOriginalWords.originalWords_injective h

theorem support_exhausted (u v w : Word) (h : CW75Primitive.tensor u v w ≠ 0) :
    ∃ a : Scalar, (x a, y a, z a) = (u, v, w) := by
  obtain ⟨terms, hterms, he⟩ := CW75Primitive.support_exhausted u v w h
  refine ⟨⟨terms, ?_⟩, he⟩
  simpa [retainedWords] using hterms

abbrev ActualSupport :=
  {uvw : Word × Word × Word // CW75Primitive.tensor uvw.1 uvw.2.1 uvw.2.2 ≠ 0}

def toActualSupport (a : Scalar) : ActualSupport :=
  ⟨(x a, y a, z a), coefficient_ne_zero a⟩

theorem toActualSupport_bijective : Function.Bijective toActualSupport := by
  constructor
  · intro a b h
    exact coordinates_injective (congrArg Subtype.val h)
  · intro s
    obtain ⟨a, ha⟩ := support_exhausted s.val.1 s.val.2.1 s.val.2.2 s.property
    exact ⟨a, Subtype.ext ha⟩

def actualSupportEquiv : Scalar ≃ ActualSupport :=
  Equiv.ofBijective toActualSupport toActualSupport_bijective

theorem actualSupport_card : Fintype.card ActualSupport = 75 := by
  rw [← Fintype.card_congr actualSupportEquiv]
  exact scalar_card

@[simp] theorem decode_original_grade (a : Scalar) :
    CWOriginalWords.decodeWord (x a) (y a) (z a) = grade a :=
  CWOriginalWords.decodeWord_originalWords (grade a)

private theorem retained_actual (a : Scalar) :
    CW75Primitive.retained (x a) (y a) (z a) := by
  by_contra h
  have hc := coefficient_one a
  simp [CW75Primitive.tensor, h] at hc

private theorem source_ne_zero (a : Scalar) :
    CW75Primitive.source (x a) (y a) (z a) ≠ 0 := by
  intro h
  have hc := coefficient_one a
  simp [CW75Primitive.tensor, h] at hc

theorem hasB_iff_not_hasC (a : Scalar) :
    CW75Primitive.hasB (x a) ↔ ¬ CW75Primitive.hasC (y a) := by
  have hr := retained_actual a
  have ha := CW75Primitive.allA_iff (x a) (y a) (z a) (source_ne_zero a)
  constructor
  · intro hb hc
    exact hr.1 ⟨hb, hc⟩
  · intro hc
    by_contra hb
    exact hr.2 (ha.mpr ⟨hb, hc⟩)

def outer (a : Scalar) : Bool := decide (CW75Primitive.hasB (x a))

def bPositions (a : Scalar) : BitWord := fun i => decide (x a i ≠ 0)
def cPositions (a : Scalar) : BitWord := fun i => decide (y a i = 2)
def aChoices (a : Scalar) : BitWord := fun i => decide (z a i = 1)
def bChoices (a : Scalar) : BitWord := fun i => decide (x a i = 1)

theorem bPositions_eq_zero_of_outer_false (a : Scalar) (h : outer a = false) :
    bPositions a = fun _ => false := by
  have hb : ¬ CW75Primitive.hasB (x a) := by simpa [outer] using h
  funext i
  have hx : x a i = 0 := by
    by_contra hn
    exact hb ⟨i, hn⟩
  simp [bPositions, hx]

theorem cPositions_eq_zero_of_outer_true (a : Scalar) (h : outer a = true) :
    cPositions a = fun _ => false := by
  have hb : CW75Primitive.hasB (x a) := by simpa [outer] using h
  have hc := (hasB_iff_not_hasC a).mp hb
  funext i
  have hy : y a i ≠ 2 := fun hn => hc ⟨i, hn⟩
  simp [cPositions, hy]

def outerX (u : Word) : Bool := decide (CW75Primitive.hasB u)
def outerY (v : Word) : Bool := !decide (CW75Primitive.hasC v)

def bPositionsX (u : Word) : BitWord := fun i => decide (u i ≠ 0)
def bPositionsZ (pb : Bool) (w : Word) : BitWord :=
  fun i => if pb then decide (w i = 0) else false

def cPositionsY (v : Word) : BitWord := fun i => decide (v i = 2)
def cPositionsZ (pb : Bool) (w : Word) : BitWord :=
  fun i => if pb then false else decide (w i = 0)

def aChoicesY (bs cs : BitWord) (v : Word) : BitWord :=
  fun i => !bs i && !cs i && decide (v i = 1)
def aChoicesZ (w : Word) : BitWord := fun i => decide (w i = 1)

def bChoicesX (u : Word) : BitWord := fun i => decide (u i = 1)
def bChoicesY (bs : BitWord) (v : Word) : BitWord :=
  fun i => bs i && decide (v i = 1)

theorem outerX_read (a : Scalar) : outerX (x a) = outer a := rfl

theorem outerY_read (a : Scalar) : outerY (y a) = outer a := by
  simp only [outerY, outer, hasB_iff_not_hasC, decide_not]

theorem bPositionsX_read (a : Scalar) : bPositionsX (x a) = bPositions a := rfl

theorem bPositionsZ_read (a : Scalar) : bPositionsZ (outer a) (z a) = bPositions a := by
  funext i
  have hactive := CW75Primitive.boundary_active (x a i) (y a i) (z a i)
    (CW75Primitive.source_factors (x a) (y a) (z a) (source_ne_zero a) i)
  by_cases hb : CW75Primitive.hasB (x a)
  · have hy : y a i ≠ 2 := fun h => (hasB_iff_not_hasC a).mp hb ⟨i, h⟩
    have he : z a i = 0 ↔ x a i ≠ 0 := by tauto
    simp [bPositionsZ, outer, bPositions, hb, he]
  · have hx : x a i = 0 := by
      by_contra h
      exact hb ⟨i, h⟩
    simp [bPositionsZ, outer, bPositions, hb, hx]

theorem cPositionsY_read (a : Scalar) : cPositionsY (y a) = cPositions a := rfl

theorem cPositionsZ_read (a : Scalar) : cPositionsZ (outer a) (z a) = cPositions a := by
  funext i
  have hactive := CW75Primitive.boundary_active (x a i) (y a i) (z a i)
    (CW75Primitive.source_factors (x a) (y a) (z a) (source_ne_zero a) i)
  by_cases hb : CW75Primitive.hasB (x a)
  · have hy : y a i ≠ 2 := fun h => (hasB_iff_not_hasC a).mp hb ⟨i, h⟩
    simp [cPositionsZ, outer, cPositions, hb, hy]
  · have hx : x a i = 0 := by
      by_contra h
      exact hb ⟨i, h⟩
    have he : z a i = 0 ↔ y a i = 2 := by tauto
    simp [cPositionsZ, outer, cPositions, hb, he]

theorem aChoicesY_read (a : Scalar) :
    aChoicesY (bPositions a) (cPositions a) (y a) = aChoices a := by
  funext i
  change (!decide ((CW75Primitive.component (letter a i)).x ≠ 0) &&
    !decide ((CW75Primitive.component (letter a i)).y = 2) &&
    decide ((CW75Primitive.component (letter a i)).y = 1)) =
    decide ((CW75Primitive.component (letter a i)).z = 1)
  cases letter a i <;>
    norm_num [CW75Primitive.component, CWOriginalWords.OriginalComponent.x,
      CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z,
      ← Fin.val_eq_val]

theorem aChoicesZ_read (a : Scalar) : aChoicesZ (z a) = aChoices a := rfl

theorem bChoicesX_read (a : Scalar) : bChoicesX (x a) = bChoices a := rfl

theorem bChoicesY_read (a : Scalar) :
    bChoicesY (bPositions a) (y a) = bChoices a := by
  funext i
  change (decide ((CW75Primitive.component (letter a i)).x ≠ 0) &&
    decide ((CW75Primitive.component (letter a i)).y = 1)) =
    decide ((CW75Primitive.component (letter a i)).x = 1)
  cases letter a i <;>
    norm_num [CW75Primitive.component, CWOriginalWords.OriginalComponent.x,
      CWOriginalWords.OriginalComponent.y, ← Fin.val_eq_val]

private theorem term_bits_injective : Function.Injective
    (fun a : BoundaryTerm =>
      (decide ((CW75Primitive.component a).x ≠ 0),
       decide ((CW75Primitive.component a).y = 2),
       decide ((CW75Primitive.component a).z = 1),
       decide ((CW75Primitive.component a).x = 1))) := by
  intro a b h
  cases a <;> cases b <;>
    norm_num [CW75Primitive.component, CWOriginalWords.OriginalComponent.x,
      CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z,
      ← Fin.val_eq_val] at h <;> rfl

theorem positionLabels_injective : Function.Injective
    (fun a : Scalar => (bPositions a, cPositions a, aChoices a, bChoices a)) := by
  intro a b h
  apply grade_injective
  funext i
  apply congrArg CW75Primitive.component
  apply term_bits_injective
  exact Prod.ext (congrFun (congrArg Prod.fst h) i)
    (Prod.ext (congrFun (congrArg (fun q => q.2.1) h) i)
      (Prod.ext (congrFun (congrArg (fun q => q.2.2.1) h) i)
        (congrFun (congrArg (fun q => q.2.2.2) h) i)))

def Label : ℕ → Type
  | 0 => Bool
  | _ + 1 => BitWord

instance labelFintype (n : ℕ) : Fintype (Label n) := by
  cases n <;> simp only [Label] <;> infer_instance

def labels : (n : ℕ) → Scalar → Label n
  | 0 => outer
  | 1 => bPositions
  | 2 => cPositions
  | 3 => aChoices
  | 4 => bChoices
  | _ + 5 => fun _ _ => false

inductive Side where
  | x | y | z
  deriving DecidableEq

def firstSide : ℕ → Side
  | 2 | 3 => .y
  | _ => .x

def secondSide : ℕ → Side
  | 1 | 2 | 3 => .z
  | _ => .y

def originalCoordinate : Side → Scalar → Word
  | .x => x
  | .y => y
  | .z => z

def firstReader : (n : ℕ) → LabelRecord Label n → Word → Label n
  | 0, _ => outerX
  | 1, _ => bPositionsX
  | 2, _ => cPositionsY
  | 3, prior => aChoicesY prior.1.2 prior.2
  | 4, _ => bChoicesX
  | _ + 5, _ => fun _ _ => false

def secondReader : (n : ℕ) → LabelRecord Label n → Word → Label n
  | 0, _ => outerY
  | 1, prior => bPositionsZ prior.2
  | 2, prior => cPositionsZ prior.1.2
  | 3, _ => aChoicesZ
  | 4, prior => bChoicesY prior.1.1.2
  | _ + 5, _ => fun _ _ => false

theorem firstReader_readable (n : ℕ) (hn : n < 5) (a : Scalar) :
    firstReader n (labelRecordOf labels n a) (originalCoordinate (firstSide n) a) =
      labels n a := by
  interval_cases n
  · exact outerX_read a
  · exact bPositionsX_read a
  · exact cPositionsY_read a
  · exact aChoicesY_read a
  · exact bChoicesX_read a

theorem secondReader_readable (n : ℕ) (hn : n < 5) (a : Scalar) :
    secondReader n (labelRecordOf labels n a) (originalCoordinate (secondSide n) a) =
      labels n a := by
  interval_cases n
  · exact outerY_read a
  · exact bPositionsZ_read a
  · exact cPositionsZ_read a
  · exact aChoicesZ_read a
  · exact bChoicesY_read a

theorem completeRecord_injective : Function.Injective (labelRecordOf labels 5) := by
  intro a b h
  apply positionLabels_injective
  exact Prod.ext (congrArg (fun q : LabelRecord Label 5 => q.1.1.1.2) h)
    (Prod.ext (congrArg (fun q : LabelRecord Label 5 => q.1.1.2) h)
      (Prod.ext (congrArg (fun q : LabelRecord Label 5 => q.1.2) h)
        (congrArg (fun q : LabelRecord Label 5 => q.2) h)))

end MatrixMultiplication.Foundation.CW75LabelHierarchy

end

end OAI
