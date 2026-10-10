import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.BinaryEncoding

namespace OAI

section

namespace KS.W01

def toComplex (z : RationalComplex) : ℂ := ⟨(z.1 : ℝ), (z.2 : ℝ)⟩

@[simp] theorem toComplex_re (z : RationalComplex) : (toComplex z).re = (z.1 : ℝ) := rfl
@[simp] theorem toComplex_im (z : RationalComplex) : (toComplex z).im = (z.2 : ℝ) := rfl

theorem toComplex_injective : Function.Injective toComplex := by
  intro z w h
  apply Prod.ext
  · exact Rat.cast_injective (congrArg Complex.re h)
  · exact Rat.cast_injective (congrArg Complex.im h)

theorem mem_range_toComplex (z : ℂ) :
    z ∈ Set.range toComplex ↔ ∃ a b : ℚ, z.re = (a : ℝ) ∧ z.im = (b : ℝ) := by
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨a, b, rfl, rfl⟩
  · rintro ⟨a, b, ha, hb⟩
    exact ⟨(a, b), Complex.ext ha.symm hb.symm⟩

def vectorToComplex {d : ℕ} (v : Fin d → RationalComplex) : Fin d → ℂ :=
  fun j => toComplex (v j)

theorem vectorToComplex_injective (d : ℕ) :
    Function.Injective (@vectorToComplex d) := by
  intro v w h
  funext j
  exact toComplex_injective (congrFun h j)

def encodeEntries (xs : List RationalComplex) : List Bool :=
  encodeNat xs.length ++ xs.flatMap encodeComplex

def readEntriesN : ℕ → List Bool → Option (List RationalComplex × List Bool)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (x, rest) ← readComplex bs
    let (xs, tail) ← readEntriesN n rest
    return (x :: xs, tail)

@[simp] theorem readEntriesN_flatMap_append (xs : List RationalComplex) (tail : List Bool) :
    readEntriesN xs.length (xs.flatMap encodeComplex ++ tail) = some (xs, tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.flatMap_cons, List.append_assoc, readEntriesN, ih]

def readEntries (bs : List Bool) : Option (List RationalComplex × List Bool) := do
  let (n, rest) ← readNat bs
  readEntriesN n rest

@[simp] theorem readEntries_encode_append (xs : List RationalComplex) (tail : List Bool) :
    readEntries (encodeEntries xs ++ tail) = some (xs, tail) := by
  simp [readEntries, encodeEntries, List.append_assoc]

theorem encodeEntries_injective : Function.Injective encodeEntries := by
  intro xs ys h
  have hx := readEntries_encode_append xs []
  have hy := readEntries_encode_append ys []
  simp only [List.append_nil] at hx hy
  rw [h, hy] at hx
  exact (congrArg Prod.fst (Option.some.inj hx)).symm

def encodeVector {d : ℕ} (v : Fin d → RationalComplex) : List Bool :=
  encodeEntries (List.ofFn v)

theorem encodeVector_injective (d : ℕ) : Function.Injective (@encodeVector d) := by
  intro v w h
  have h' := encodeEntries_injective h
  have : List.ofFn v = List.ofFn w := h'
  exact List.ofFn_injective this

theorem encodeComplex_length_pos (z : RationalComplex) : 0 < (encodeComplex z).length := by
  rw [length_encodeComplex, length_encodeRat, length_encodeRat]
  omega

theorem entries_count_le_bits (xs : List RationalComplex) :
    xs.length ≤ (xs.flatMap encodeComplex).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := encodeComplex_length_pos x
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

end KS.W01

end

end OAI
