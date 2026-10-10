import OAI.GroupTheory.PolycyclicRecognition.Analysis.IndependentSupportedSampling

namespace OAI

/-! # Independent suffix sampling with eventual support conditions -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The initial finitely many laws need not be carried by the permitted
sets. The same selection argument applies after the eventual support bound. -/
theorem independent_eventually_supported_bad_probability_tendsto_zero
    {A K : ℕ → Type*} [∀ n, MeasurableSpace (A n)] [∀ n, MeasurableSpace (K n)]
    (μ : ∀ n, ProbabilityMeasure (A n)) (ν : ∀ n, ProbabilityMeasure (K n))
    (D : ∀ n, Set (K n)) (hne : ∀ n, (D n).Nonempty)
    (hcarried : ∀ᶠ n in atTop, ∀ᵐ k ∂(ν n : Measure (K n)), k ∈ D n)
    (B : ∀ n, Set (A n × K n)) (hB : ∀ n, MeasurableSet (B n))
    (hp : ∀ k : ∀ n, K n, (∀ n, k n ∈ D n) →
      Tendsto (fun n => (μ n : Measure (A n)) ((fun a => (a, k n)) ⁻¹' B n))
        atTop (𝓝 0)) :
    Tendsto (fun n => (μ n : Measure (A n)).prod (ν n : Measure (K n)) (B n))
      atTop (𝓝 0) := by
  let : ∀ n, Nonempty (D n) := fun n => (hne n).to_subtype
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact False.elim ((not_lt_of_ge bot_le) hc)
  · intro c hc
    obtain ⟨d, hd0, hdc⟩ := exists_between hc
    have hb := eventually_uniform_lt_of_all_selections
      (fun n (k : D n) => (μ n : Measure (A n)) ((fun a => (a, k.val)) ⁻¹' B n))
      (fun k => hp (fun n => (k n).val) (fun n => (k n).property)) hd0
    filter_upwards [hb, hcarried] with n hn hν
    apply lt_of_le_of_lt _ hdc
    rw [Measure.prod_apply_symm (hB n)]
    calc
      _ ≤ ∫⁻ _, d ∂(ν n : Measure (K n)) := by
        apply lintegral_mono_ae
        filter_upwards [hν] with k hk
        exact (hn ⟨k, hk⟩).le
      _ = d := by simp

/-- Choose the actual eventual geometric witnesses, filling unused early
indices arbitrarily. -/
theorem exists_eventually_chosen_sequence
    {X : ℕ → Type*} [∀ n, Nonempty (X n)] (P : ∀ n, X n → Prop)
    (hP : ∀ᶠ n in atTop, ∃ x, P n x) :
    ∃ x : ∀ n, X n, ∀ᶠ n in atTop, P n (x n) := by
  classical
  let x := fun n => if h : ∃ x, P n x then h.choose else Classical.choice (inferInstance : Nonempty (X n))
  refine ⟨x, ?_⟩
  filter_upwards [hP] with n hn
  dsimp only [x]
  rw [dite_eq_left hn]
  exact hn.choose_spec

end PolycyclicRecognition

end

end OAI
