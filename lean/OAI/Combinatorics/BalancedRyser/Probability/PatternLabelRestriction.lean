import OAI.Combinatorics.BalancedRyser.Probability.PatternTailAsymptotics

namespace OAI

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Balanced.PatternModel

universe u v

noncomputable section

def restrictLabels (P : PatternModel.{u}) (A : Finset P.Label) : PatternModel.{u} := by
  classical
  exact
    { Color := P.Color
      Value := P.Value
      law := P.law
      Label := {a : P.Label // a ∈ A}
      support := fun a => P.support a.val
      event := fun a => P.event a.val
      eventMeasurable := fun a => P.eventMeasurable a.val
      dependsOn := fun a => P.dependsOn a.val }

@[simp] theorem restrictLabels_measure (P : PatternModel.{u}) (A : Finset P.Label) :
    (P.restrictLabels A).measure = P.measure := rfl

@[simp] theorem restrictLabels_fixCoordinates (P : PatternModel.{u}) (A : Finset P.Label)
    (K : Finset P.Color) (x ω : P.Sample) :
    (P.restrictLabels A).fixCoordinates K x ω = P.fixCoordinates K x ω := rfl

@[simp] theorem restrictLabels_fixedExpectation (P : PatternModel.{u}) (A : Finset P.Label)
    (K : Finset P.Color) (x : P.Sample) (f : P.Sample → ℝ) :
    (P.restrictLabels A).fixedExpectation K x f = P.fixedExpectation K x f := rfl

@[simp] theorem restrictLabels_indicator (P : PatternModel.{u}) (A : Finset P.Label)
    (a : (P.restrictLabels A).Label) (ω : P.Sample) :
    (P.restrictLabels A).indicator a ω = P.indicator a.val ω := rfl

@[simp] theorem restrictLabels_support (P : PatternModel.{u}) (A : Finset P.Label)
    (a : (P.restrictLabels A).Label) :
    (P.restrictLabels A).support a = P.support a.val := rfl

theorem restrictLabels_count (P : PatternModel.{u}) (A : Finset P.Label) (ω : P.Sample) :
    (P.restrictLabels A).count ω = ∑ a ∈ A, P.indicator a ω := by
  classical
  change (∑ a : {a : P.Label // a ∈ A}, P.indicator a.val ω) = _
  exact Finset.sum_coe_sort A (fun a => P.indicator a ω)

theorem restrictLabels_count_fun (P : PatternModel.{u}) (A : Finset P.Label) :
    (P.restrictLabels A).count = fun ω => ∑ a ∈ A, P.indicator a ω :=
  funext (P.restrictLabels_count A)

theorem restrictLabels_overlapCount (P : PatternModel.{u}) (A : Finset P.Label)
    (K₀ K : Finset P.Color) (ω : P.Sample) :
    (P.restrictLabels A).overlapCount K₀ K ω =
      ∑ a ∈ A, if Disjoint (P.support a \ K₀) K then 0 else P.indicator a ω := by
  classical
  change (∑ a : {a : P.Label // a ∈ A},
    if Disjoint (P.support a.val \ K₀) K then 0 else P.indicator a.val ω) = _
  exact Finset.sum_coe_sort A (fun a => if Disjoint (P.support a \ K₀) K
    then 0 else P.indicator a ω)

theorem restrictLabels_support_card_le (P : PatternModel.{u}) (A : Finset P.Label)
    (r : ℕ) (hr : ∀ a, (P.support a).card ≤ r) :
    ∀ a, ((P.restrictLabels A).support a).card ≤ r := fun a => hr a.val

theorem restrictLabels_count_mem_Icc (P : PatternModel.{u}) (A : Finset P.Label)
    (ω : P.Sample) :
    (P.restrictLabels A).count ω ∈ Set.Icc (0 : ℝ) (A.card : ℝ) := by
  have h := PatternTails.count_mem_Icc (P.restrictLabels A) ω
  change (P.restrictLabels A).count ω ∈ Set.Icc (0 : ℝ) (Fintype.card ↥A : ℝ) at h
  simpa only [Fintype.card_coe] using h

theorem restrictLabels_count_le (P : PatternModel.{u}) (A : Finset P.Label)
    (ω : P.Sample) : (P.restrictLabels A).count ω ≤ P.count ω := by
  classical
  rw [P.restrictLabels_count A ω]
  exact Finset.sum_le_univ_sum_of_nonneg (fun a => P.indicator_nonneg a ω)

end
end Balanced.PatternModel

namespace Balanced.PatternTails

universe u v

theorem restricted_family_raw_tail
    (P : ℕ → PatternModel.{u}) (K : ∀ q, Finset (P q).Color)
    (I : ℕ → Type v) [∀ q, Fintype (I q)]
    (A : ∀ q, I q → Finset (P q).Label) (d : ℕ)
    (hcard : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ q, N ≤ q →
      (Fintype.card (I q) : ℝ) ≤ c * (q : ℝ) ^ d)
    (hmom : ∀ s : ℕ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ q, N ≤ q → ∀ x : (P q).Sample, ∀ i,
        ((P q).restrictLabels (A q i)).fixedExpectation (K q) x
          (fun ω => ((P q).restrictLabels (A q i)).count ω ^ s) ≤ C)
    (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q, N ≤ q → ∀ x : (P q).Sample,
      (P q).measure.real {ω | ∃ i, (q : ℝ) ^ ((1 : ℝ) / 100) ≤
        ∑ a ∈ A q i, (P q).indicator a ((P q).fixCoordinates (K q) x ω)} ≤
          C / (q : ℝ) ^ k := by
  have h := uniform_polynomial_raw_tail P K I
    (fun q i => ((P q).restrictLabels (A q i)).count)
    (fun q i => ((P q).restrictLabels (A q i)).measurable_count)
    (fun q i ω => ((P q).restrictLabels_count_mem_Icc (A q i) ω).1)
    (fun q i => ((A q i).card : ℝ))
    (fun q i ω => ((P q).restrictLabels_count_mem_Icc (A q i) ω).2)
    d hcard hmom k hk
  simpa only [PatternModel.restrictLabels_count_fun] using h

theorem restricted_family_centered_tail
    (P : ℕ → PatternModel.{u}) (K : ∀ q, Finset (P q).Color)
    (I : ℕ → Type v) [∀ q, Fintype (I q)]
    (A : ∀ q, I q → Finset (P q).Label) (d : ℕ)
    (hcard : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ q, N ≤ q →
      (Fintype.card (I q) : ℝ) ≤ c * (q : ℝ) ^ d)
    (hmom : ∀ s : ℕ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ q, N ≤ q → ∀ x : (P q).Sample, ∀ i,
        ((P q).restrictLabels (A q i)).fixedExpectation (K q) x
          (fun ω => |((P q).restrictLabels (A q i)).count ω -
            ((P q).restrictLabels (A q i)).fixedExpectation (K q) x
              ((P q).restrictLabels (A q i)).count| ^ (2 * s)) ≤ C * (q : ℝ) ^ s)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q, N ≤ q → ∀ x : (P q).Sample,
      (P q).measure.real {ω | ∃ i, ε * (q : ℝ) ≤
        |(∑ a ∈ A q i, (P q).indicator a ((P q).fixCoordinates (K q) x ω)) -
          (P q).fixedExpectation (K q) x
            (fun η => ∑ a ∈ A q i, (P q).indicator a η)|} ≤ C / (q : ℝ) ^ k := by
  have h := uniform_polynomial_centered_tail P K I
    (fun q i => ((P q).restrictLabels (A q i)).count)
    (fun q i => ((P q).restrictLabels (A q i)).measurable_count)
    (fun q i => ((A q i).card : ℝ))
    (fun q i ω => by
      rw [abs_of_nonneg ((P q).restrictLabels_count_mem_Icc (A q i) ω).1]
      exact ((P q).restrictLabels_count_mem_Icc (A q i) ω).2)
    d hcard hmom ε hε k hk
  simpa only [PatternModel.restrictLabels_count_fun] using h

end Balanced.PatternTails

end OAI
