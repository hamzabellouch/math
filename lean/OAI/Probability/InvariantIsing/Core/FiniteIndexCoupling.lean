import OAI.Probability.InvariantIsing.Core.FiniteIndexDistribution

namespace OAI

/-! Joint finite random labels give exact nonnegative transport plans. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace InvariantIsing

variable {Ω A B : Type*} [MeasurableSpace Ω] [Fintype A] [Fintype B]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [MeasurableSingletonClass B]

def finiteIndexCoupling (P : Measure Ω) (g : Ω → A) (h : Ω → B) (a : A) (b : B) : ℝ :=
  P.real ((g ⁻¹' {a}) ∩ (h ⁻¹' {b}))

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma finiteIndexCoupling_row (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → A) (h : Ω → B) (hh : Measurable h) (a : A) :
    ∑ b, finiteIndexCoupling P g h a b=finiteIndexWeight P g a := by
  have hs := sum_measureReal_preimage_singleton (μ := P.restrict (g ⁻¹' {a}))
    Finset.univ (f := h) (fun b _ => hh (measurableSet_singleton b))
  simp only [measureReal_restrict_apply (hh (measurableSet_singleton _)),
    Finset.coe_univ,preimage_univ,measureReal_restrict_apply_univ] at hs
  simpa only [finiteIndexCoupling,finiteIndexWeight,inter_comm] using hs

omit [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] in
lemma finiteIndexCoupling_col (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → A) (h : Ω → B) (hg : Measurable g) (b : B) :
    ∑ a, finiteIndexCoupling P g h a b=finiteIndexWeight P h b := by
  simpa only [finiteIndexCoupling,inter_comm] using finiteIndexCoupling_row P h g hg b

lemma finiteIndexCoupling_integral (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → A) (h : Ω → B) (hg : Measurable g) (hh : Measurable h)
    (f : A → B → ℝ) :
    (∫ x, f (g x) (h x) ∂P)=∑ a, ∑ b, finiteIndexCoupling P g h a b*f a b := by
  let T := fun a b => (g ⁻¹' {a}) ∩ (h ⁻¹' {b})
  have hT a b : MeasurableSet (T a b) :=
    (hg (measurableSet_singleton a)).inter (hh (measurableSet_singleton b))
  have hf : (fun x => f (g x) (h x))=
      fun x => ∑ a, ∑ b, (T a b).indicator (fun _ => f a b) x := by
    funext x
    simp [T,Set.indicator_apply,ite_and]
  rw [hf,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro b _
      rw [integral_indicator_const _ (hT a b)]
      rfl
    · intro b _
      exact (integrable_const _).indicator (hT a b)
  · intro a _
    exact integrable_finsetSum _ (fun b _ => (integrable_const _).indicator (hT a b))

end InvariantIsing

end

end OAI
