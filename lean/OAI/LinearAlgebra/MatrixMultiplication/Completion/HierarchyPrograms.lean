import OAI.LinearAlgebra.MatrixMultiplication.Completion.HierarchyWords
import OAI.LinearAlgebra.MatrixMultiplication.Completion.Labels

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionHierarchyWords

open MatrixMultiplication.Foundation

universe u v p q

variable {A : Type u}

namespace ReadableHierarchy

open RecursiveCompletion CompletionLabels.TopologicalFlatten

def ofProgram {Coord : Color → Type v} {Context : Type q} {Code : Type p}
    [Fintype Code] {depth : ℕ} (s : Program A Coord Context Code depth)
    (ctx : Context) (hctx : ∀ a, s.context a = ctx)
    (joint : Function.Injective (fun a => (s.view .B a, s.view .C a, s.view .A a))) :
    ReadableHierarchy A (Coord .B) (Coord .C) (Coord .A) where
  Label := fun _ => Code
  fintypeLabel := fun _ => inferInstance
  labels := s.labels
  depth := depth
  pair := s.pair
  x := s.view .B
  y := s.view .C
  z := s.view .A
  coordinates_injective := joint
  readXYX n _ prior own := s.read n .B ctx (Program.recordArray n prior) own
  readXYY n _ prior own := s.read n .C ctx (Program.recordArray n prior) own
  readXZX n _ prior own := s.read n .B ctx (Program.recordArray n prior) own
  readXZZ n _ prior own := s.read n .A ctx (Program.recordArray n prior) own
  readYZY n _ prior own := s.read n .C ctx (Program.recordArray n prior) own
  readYZZ n _ prior own := s.read n .A ctx (Program.recordArray n prior) own
  readXYX_readable n hn hp a := by
    change s.read n .B ctx (Program.recordArray n (labelRecordOf s.labels n a))
      (s.view .B a) = s.labels n a
    rw [Program.recordArray_labelRecordOf, ← hctx a]
    exact s.readable n hn a .B (Or.inl (by simp only [hp, firstSide]))
  readXYY_readable n hn hp a := by
    change s.read n .C ctx (Program.recordArray n (labelRecordOf s.labels n a))
      (s.view .C a) = s.labels n a
    rw [Program.recordArray_labelRecordOf, ← hctx a]
    exact s.readable n hn a .C (Or.inr (by simp only [hp, secondSide]))
  readXZX_readable n hn hp a := by
    change s.read n .B ctx (Program.recordArray n (labelRecordOf s.labels n a))
      (s.view .B a) = s.labels n a
    rw [Program.recordArray_labelRecordOf, ← hctx a]
    exact s.readable n hn a .B (Or.inl (by simp only [hp, firstSide]))
  readXZZ_readable n hn hp a := by
    change s.read n .A ctx (Program.recordArray n (labelRecordOf s.labels n a))
      (s.view .A a) = s.labels n a
    rw [Program.recordArray_labelRecordOf, ← hctx a]
    exact s.readable n hn a .A (Or.inr (by simp only [hp, secondSide]))
  readYZY_readable n hn hp a := by
    change s.read n .C ctx (Program.recordArray n (labelRecordOf s.labels n a))
      (s.view .C a) = s.labels n a
    rw [Program.recordArray_labelRecordOf, ← hctx a]
    exact s.readable n hn a .C (Or.inl (by simp only [hp, firstSide]))
  readYZZ_readable n hn hp a := by
    change s.read n .A ctx (Program.recordArray n (labelRecordOf s.labels n a))
      (s.view .A a) = s.labels n a
    rw [Program.recordArray_labelRecordOf, ← hctx a]
    exact s.readable n hn a .A (Or.inr (by simp only [hp, secondSide]))

theorem ofProgram_complete {Coord : Color → Type v} {Context : Type q} {Code : Type p}
    [Fintype Code] {depth : ℕ} (s : Program A Coord Context Code depth)
    (ctx : Context) (hctx : ∀ a, s.context a = ctx)
    (joint : Function.Injective (fun a => (s.view .B a, s.view .C a, s.view .A a)))
    (complete : s.Complete) :
    Function.Injective (labelRecordOf (ofProgram s ctx hctx joint).labels depth) := by
  intro a b h
  apply complete a b ((hctx a).trans (hctx b).symm)
  intro n hn
  exact label_eq_of_record_eq s.labels h hn

end ReadableHierarchy

end MatrixMultiplication.CompletionHierarchyWords

end

end OAI
