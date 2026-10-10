import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

namespace OAI

/-! # Measurable orthogonal frames for projection fields

A countable family of measurable vectors can be orthogonalized measurably,
including at points where its rank changes. Zero vectors are retained until
the dimension strata are selected.
-/

namespace KadisonKastler

open MeasureTheory InnerProductSpace

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem measurable_gramSchmidt_sequence (v : X → ℕ → H)
    (hv : ∀ n, Measurable fun x => v x n) (n : ℕ) :
    Measurable fun x => gramSchmidt ℂ (v x) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    simp_rw [gramSchmidt_def ℂ _ n]
    simp_rw [Submodule.starProjection_singleton]
    apply (hv n).sub
    apply Finset.measurable_sum
    intro i hi
    have hm := ih i (Finset.mem_Iio.mp hi)
    exact ((hm.inner (hv n)).div
      (Complex.continuous_ofReal.measurable.comp (hm.norm.pow_const 2))).smul hm

theorem measurable_gramSchmidtNormed_sequence (v : X → ℕ → H)
    (hv : ∀ n, Measurable fun x => v x n) (n : ℕ) :
    Measurable fun x => gramSchmidtNormed ℂ (v x) n := by
  have hm := measurable_gramSchmidt_sequence v hv n
  exact ((Complex.continuous_ofReal.measurable.comp hm.norm).inv).smul hm

/-- The normalized Gram-Schmidt vectors of a measurable projection field. -/
def measurableProjectionFrame (P : X → H →L[ℂ] H) (b : ℕ → H) (x : X) (n : ℕ) : H :=
  gramSchmidtNormed ℂ (fun i => P x (b i)) n

theorem measurableProjectionFrame_measurable (P : X → H →L[ℂ] H) (b : ℕ → H)
    (hP : ∀ v : H, Measurable fun x => P x v) (n : ℕ) :
    Measurable fun x => measurableProjectionFrame P b x n :=
  measurable_gramSchmidtNormed_sequence _ (fun i => hP (b i)) n

omit [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
theorem measurableProjectionFrame_orthonormal (P : X → H →L[ℂ] H) (b : ℕ → H) (x : X) :
    Orthonormal ℂ (fun i : {n | measurableProjectionFrame P b x n ≠ 0} =>
      measurableProjectionFrame P b x i) :=
  gramSchmidtNormed_orthonormal' (𝕜 := ℂ) (fun i => P x (b i))

/- The input can be any countable total sequence, with no independence assumption. -/
omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
 theorem projectedTotalSequence (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range fun n => P (b n))).topologicalClosure = P.range := by
  have he : (Submodule.span ℂ (Set.range b)).map P.toLinearMap =
      Submodule.span ℂ (Set.range fun n => P (b n)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hl := Submodule.topologicalClosure_map P (Submodule.span ℂ (Set.range b))
  rw [hb, Submodule.map_top, he] at hl
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact ⟨b n, rfl⟩
    · exact ContinuousLinearMap.IsIdempotentElem.isClosed_range hP
  · exact hl

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
 theorem projectionFrame_total_of_total (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ (fun n => P (b n))))).topologicalClosure =
      P.range := by
  rw [span_gramSchmidtNormed_range, span_gramSchmidt]
  exact projectedTotalSequence P hP b hb

/- Projecting a Hilbert basis gives a total family in the closed range. -/
omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
 theorem projectedHilbertBasis_total (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : HilbertBasis ℕ ℂ H) :
    (Submodule.span ℂ (Set.range fun n => P (b n))).topologicalClosure = P.range := by
  have he : (Submodule.span ℂ (Set.range b)).map P.toLinearMap =
      Submodule.span ℂ (Set.range fun n => P (b n)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hl := Submodule.topologicalClosure_map P (Submodule.span ℂ (Set.range b))
  rw [b.dense_span, Submodule.map_top, he] at hl
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact ⟨b n, rfl⟩
    · exact ContinuousLinearMap.IsIdempotentElem.isClosed_range hP
  · exact hl

/- Removing zero Gram-Schmidt vectors preserves totality in a projection range. -/
omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
 theorem projectionFrame_total (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : HilbertBasis ℕ ℂ H) :
    (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ (fun n => P (b n))))).topologicalClosure =
      P.range := by
  rw [span_gramSchmidtNormed_range, span_gramSchmidt]
  exact projectedHilbertBasis_total P hP b

end

end KadisonKastler

end OAI
