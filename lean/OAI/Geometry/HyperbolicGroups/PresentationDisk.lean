import Mathlib
import OAI.Geometry.HyperbolicGroups.Presentation
import OAI.Geometry.HyperbolicGroups.WordDisk

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace LetterPresentation
open IncidenceTemplate MasterGraph
variable (n : ℕ)

lemma freeLetter_mk (a : Alphabet n) : freeLetter n a = FreeGroup.mk [a] := by
  rcases a with ⟨i,b⟩
  cases b <;> rfl

lemma mk_prod (w : List (Alphabet n)) :
    FreeGroup.mk w = (w.map (freeLetter n)).prod := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change FreeGroup.mk ([a]++w) = freeLetter n a * (w.map (freeLetter n)).prod
    rw [← FreeGroup.mul_mk,← freeLetter_mk,ih]

def stepLetter {a b : MasterGraph.Vertex} (l : Field → Alphabet n) (s : MasterGraph.Step a b) :
    Alphabet n := if s.forward then l s.field else inverseLetter n (l s.field)

lemma mk_stepLetter {a b : MasterGraph.Vertex} (l : Field → Alphabet n) (s : MasterGraph.Step a b) :
    FreeGroup.mk [stepLetter n l s] = s.value l (freeLetter n) := by
  rw [← freeLetter_mk]
  cases h : s.forward <;> simp [stepLetter,Step.value,h,freeLetter_inv]

def pathWord (l : Field → Alphabet n) : {a b : MasterGraph.Vertex} → MasterGraph.Path a b → List (Alphabet n)
  | _,_,.nil _ => []
  | _,_,.cons s p => stepLetter n l s :: pathWord l p

lemma pathWord_length {a b : MasterGraph.Vertex} (l : Field → Alphabet n) (p : MasterGraph.Path a b) :
    (pathWord n l p).length = p.length := by
  induction p with
  | nil => rfl
  | cons s p ih => simp [pathWord,Path.length,ih]

lemma mk_pathWord {a b : MasterGraph.Vertex} (l : Field → Alphabet n) (p : MasterGraph.Path a b) :
    FreeGroup.mk (pathWord n l p) = p.eval l (freeLetter n) := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    change FreeGroup.mk ([stepLetter n l s] ++ pathWord n l p) = _
    rw [← FreeGroup.mul_mk,mk_stepLetter,ih]
    rfl

def literalSquare (l : Field → Alphabet n) (τ : TwoPath) : List (Alphabet n) :=
  [stepLetter n l (first τ), stepLetter n l (second τ), l (.inr (τ,0)), l (.inr (τ,1))]

lemma mk_literalSquare (l : Field → Alphabet n) (τ : TwoPath) :
    FreeGroup.mk (literalSquare n l τ) = squareWord l (freeLetter n) τ := by
  rw [mk_prod]
  simp only [literalSquare,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rw [freeLetter_mk,freeLetter_mk,mk_stepLetter,mk_stepLetter]
  simp only [squareWord,mul_assoc]

variable (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Literal boundaries, retaining every side index of its graph walk or row.
The arbitrary fan/top walks will later be reduced to a finite list of defining
cycles; the disk theorem here has no area estimate. -/
inductive WordRelator : List (Alphabet n) → Prop
  | fan (l : Field → Alphabet n) (i : Fin 7)
      (present : w (TableModel.row rowSupport l (.inl i)) = true)
      (v : MasterGraph.Vertex) (p : MasterGraph.Path v v)
      (fields : p.fields.toFinset ⊆ rowSupport (.inl i)) : WordRelator (pathWord n l p)
  | top (l : Field → Alphabet n)
      (present : w (TableModel.row rowSupport l (.inr (.inl ()))) = true)
      (fans : ∀ i : Fin 7, w (TableModel.row rowSupport l (.inl i)) = true)
      (v : MasterGraph.Vertex) (p : MasterGraph.Path v v) (core : p.IsCore) :
      WordRelator (pathWord n l p)
  | square (l : Field → Alphabet n) (τ : TwoPath)
      (present : w (TableModel.row rowSupport l (.inr (.inr τ))) = true) :
      WordRelator (literalSquare n l τ)
  | six (x : Fin 6 → Alphabet n) (present : d x = true) : WordRelator (List.ofFn x)

lemma mk_ofFn (x : Fin 6 → Alphabet n) :
    FreeGroup.mk (List.ofFn x) = (List.ofFn (freeLetter n ∘ x)).prod := by
  rw [mk_prod,List.map_ofFn]

lemma wordRelator_image : FreeGroup.mk '' WordRelator n w d = Relator n w d := by
  ext g
  constructor
  · rintro ⟨v,hv,rfl⟩
    cases hv with
    | fan l i present v p fields =>
      rw [mk_pathWord]
      exact Relator.fan l i present v p fields
    | top l present fans v p core =>
      rw [mk_pathWord]
      exact Relator.top l present fans v p core
    | square l τ present =>
      rw [mk_literalSquare]
      exact Relator.square l τ present
    | six x present =>
      rw [mk_ofFn]
      exact Relator.six x present
  · intro hg
    cases hg with
    | fan l i present v p fields =>
      exact ⟨_,WordRelator.fan l i present v p fields,mk_pathWord n l p⟩
    | top l present fans v p core =>
      exact ⟨_,WordRelator.top l present fans v p core,mk_pathWord n l p⟩
    | square l τ present =>
      exact ⟨_,WordRelator.square l τ present,mk_literalSquare n l τ⟩
    | six x present => exact ⟨_,WordRelator.six x present,mk_ofFn n x⟩

/-- Every null literal letter word has a finite disk derivation over the
actual included fan/top/decorations, with free cancellations accounted for at
zero cost. This is the algebraic part of source diagram:existence. -/
theorem null_word_disk (z : List (Alphabet n))
    (hz : PresentedGroup.mk (Relator n w d) (FreeGroup.mk z) = 1) :
    ∃ a, WordPictures.Homotopy (WordRelator n w d) z [] a := by
  apply WordPictures.existence z
  rwa [wordRelator_image]

end LetterPresentation
end HyperbolicObstruction
end
end

section

end
end

end OAI
