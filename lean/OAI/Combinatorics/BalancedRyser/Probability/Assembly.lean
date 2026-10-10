import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace OAI

open Filter MeasureTheory
open scoped Topology

namespace Balanced.Assembly

theorem measureReal_le_good_add_three_errors {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A E₁ E₂ E₃ : Set Ω) :
    μ.real A ≤ μ.real (A \ (E₁ ∪ E₂ ∪ E₃)) +
      (μ.real (A ∩ E₁) + μ.real (A ∩ E₂) + μ.real (A ∩ E₃)) := by
  have hsub : A ⊆ (A \ (E₁ ∪ E₂ ∪ E₃)) ∪ ((A ∩ E₁) ∪ (A ∩ E₂) ∪ (A ∩ E₃)) := by
    intro x hx
    by_cases hbad : x ∈ E₁ ∪ E₂ ∪ E₃
    · right
      rcases hbad with (h₁ | h₂) | h₃
      · exact Or.inl (Or.inl ⟨hx, h₁⟩)
      · exact Or.inl (Or.inr ⟨hx, h₂⟩)
      · exact Or.inr ⟨hx, h₃⟩
    · exact Or.inl ⟨hx, hbad⟩
  have hmono := measureReal_mono (μ := μ) hsub
  have hsplit := measureReal_union_le (μ := μ)
    (A \ (E₁ ∪ E₂ ∪ E₃)) ((A ∩ E₁) ∪ (A ∩ E₂) ∪ (A ∩ E₃))
  have h23 := measureReal_union_le (μ := μ) ((A ∩ E₁) ∪ (A ∩ E₂)) (A ∩ E₃)
  have h12 := measureReal_union_le (μ := μ) (A ∩ E₁) (A ∩ E₂)
  linarith

theorem positive_measureReal_good_of_three_errors_lt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A E₁ E₂ E₃ : Set Ω)
    (h : μ.real (A ∩ E₁) + μ.real (A ∩ E₂) + μ.real (A ∩ E₃) < μ.real A) :
    0 < μ.real (A \ (E₁ ∪ E₂ ∪ E₃)) := by
  have := measureReal_le_good_add_three_errors μ A E₁ E₂ E₃
  linarith

theorem eventually_positive_measureReal_good
    {ι : Type*} {l : Filter ι} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    [∀ i, IsFiniteMeasure (μ i)] (A E₁ E₂ E₃ : ∀ i, Set (Ω i))
    {c : ℝ} (hc : 0 < c) (hA : ∀ᶠ i in l, c ≤ (μ i).real (A i))
    (h₁ : Tendsto (fun i => (μ i).real (A i ∩ E₁ i)) l (𝓝 0))
    (h₂ : Tendsto (fun i => (μ i).real (A i ∩ E₂ i)) l (𝓝 0))
    (h₃ : Tendsto (fun i => (μ i).real (A i ∩ E₃ i)) l (𝓝 0)) :
    ∀ᶠ i in l, 0 < (μ i).real (A i \ (E₁ i ∪ E₂ i ∪ E₃ i)) := by
  have hsum : Tendsto (fun i => (μ i).real (A i ∩ E₁ i) +
      (μ i).real (A i ∩ E₂ i) + (μ i).real (A i ∩ E₃ i)) l (𝓝 0) := by
    simpa only [add_zero] using (h₁.add h₂).add h₃
  filter_upwards [hA, hsum.eventually_lt_const hc] with i hAi hi
  exact positive_measureReal_good_of_three_errors_lt (μ i) (A i) (E₁ i) (E₂ i) (E₃ i)
    (hi.trans_le hAi)

theorem eventually_exists_good
    {ι : Type*} {l : Filter ι} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    [∀ i, IsFiniteMeasure (μ i)] (A E₁ E₂ E₃ : ∀ i, Set (Ω i))
    {c : ℝ} (hc : 0 < c) (hA : ∀ᶠ i in l, c ≤ (μ i).real (A i))
    (h₁ : Tendsto (fun i => (μ i).real (A i ∩ E₁ i)) l (𝓝 0))
    (h₂ : Tendsto (fun i => (μ i).real (A i ∩ E₂ i)) l (𝓝 0))
    (h₃ : Tendsto (fun i => (μ i).real (A i ∩ E₃ i)) l (𝓝 0)) :
    ∀ᶠ i in l, ∃ ω ∈ A i, ω ∉ E₁ i ∧ ω ∉ E₂ i ∧ ω ∉ E₃ i := by
  filter_upwards [eventually_positive_measureReal_good μ A E₁ E₂ E₃ hc hA h₁ h₂ h₃]
    with i hi
  have hne : (A i \ (E₁ i ∪ E₂ i ∪ E₃ i)).Nonempty := by
    by_contra h
    have hempty := Set.not_nonempty_iff_eq_empty.mp h
    simp only [hempty, measureReal_empty, lt_self_iff_false] at hi
  rcases hne with ⟨ω, hω, hgood⟩
  exact ⟨ω, hω, by simpa only [Set.mem_union, not_or, and_assoc] using hgood⟩

end Balanced.Assembly

end OAI
