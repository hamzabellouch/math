import OAI.LinearAlgebra.MatrixMultiplication.Completion.Labels
import OAI.LinearAlgebra.MatrixMultiplication.Duality.Information

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten.TopologicalSchedule

open MatrixMultiplication.Foundation RecursiveCompletion DualInformation

universe u v

variable {A : Type u} [Fintype A] {Coord : Color → Type v}
  [Fintype (Coord .B)] {depth : ℕ}

theorem incident_rate_eq_x_entropy (s : TopologicalSchedule A Coord depth)
    (p : FiniteLaw A) (complete : s.toNodeSchedule.Complete depth)
    (independent : ∀ n : Fin depth, s.pairs n = .yz →
      ConditionalIndependent p (labelRecordOf s.toNodeSchedule.labels n.val)
        (s.toNodeSchedule.labels n.val) (s.view .B)) :
    ConditionalLabels.lawPairingRate p s.toNodeSchedule.labels depth s.pairs .xy +
      ConditionalLabels.lawPairingRate p s.toNodeSchedule.labels depth s.pairs .xz =
        finiteEntropy (p.map (s.view .B)).mass := by
  apply incident_rate_eq_coordinate_entropy p s.toNodeSchedule.labels depth s.pairs
    (s.view .B) (s.completeRecord_injective complete) ?_ independent
  intro n hn
  have hs : firstSide (s.readerPair n.val) = .B := by
    cases hr : s.readerPair n.val <;> simp_all [pairs, firstSide]
  let read : LabelRecord s.toNodeSchedule.Label n.val → Coord .B →
      s.toNodeSchedule.Label n.val := fun r x =>
        s.firstReader n.val r (hs.symm ▸ x)
  refine ⟨fun rx => read rx.1 rx.2, ?_⟩
  intro a
  have transport (c d : Color) (h : c = d) :
      h.symm ▸ s.view d a = s.view c a := by
    cases h
    rfl
  have hv : hs.symm ▸ s.view .B a = s.view (firstSide (s.readerPair n.val)) a :=
    transport _ _ hs
  change s.firstReader n.val (labelRecordOf s.toNodeSchedule.labels n.val a)
    (hs.symm ▸ s.view .B a) = s.toNodeSchedule.labels n.val a
  rw [hv]
  exact s.firstReader_readable n.val n.isLt a

end MatrixMultiplication.CompletionLabels.TopologicalFlatten.TopologicalSchedule

namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program

open MatrixMultiplication.Foundation RecursiveCompletion DualInformation

universe u v w z

variable {A : Type u} [Fintype A] {Coord : Color → Type v}
  [Fintype (Coord .B)] {Context : Type z} {Code : Type w} [Fintype Code]
  {depth : ℕ}

theorem incident_rate_eq_x_entropy (s : Program A Coord Context Code depth)
    (p : FiniteLaw A) (complete : s.Complete) (ctx : Context)
    (context_constant : ∀ a, s.context a = ctx)
    (independent : ∀ n : Fin depth, s.pair n.val = .yz →
      ConditionalIndependent p (labelRecordOf s.labels n.val)
        (s.labels n.val) (s.view .B)) :
    ConditionalLabels.lawPairingRate p s.labels depth (fun n => s.pair n.val) .xy +
      ConditionalLabels.lawPairingRate p s.labels depth (fun n => s.pair n.val) .xz =
        finiteEntropy (p.map (s.view .B)).mass := by
  have hinj : Function.Injective (labelRecordOf s.labels depth) := by
    intro a b h
    apply complete a b ((context_constant a).trans (context_constant b).symm)
    intro n hn
    exact label_eq_of_record_eq s.labels h hn
  apply incident_rate_eq_coordinate_entropy p s.labels depth (fun n => s.pair n.val)
    (s.view .B) hinj ?_ independent
  intro n hn
  have hs : .B = firstSide (s.pair n.val) := by
    cases hr : s.pair n.val <;> simp_all [firstSide]
  refine ⟨fun rx => s.read n.val .B ctx (recordArray n.val rx.1) rx.2, ?_⟩
  intro a
  change s.read n.val .B ctx (recordArray n.val (labelRecordOf s.labels n.val a))
    (s.view .B a) = s.labels n.val a
  rw [recordArray_labelRecordOf]
  rw [← context_constant a]
  exact s.readable n.val n.isLt a .B (Or.inl hs)

end MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program

end

end OAI
