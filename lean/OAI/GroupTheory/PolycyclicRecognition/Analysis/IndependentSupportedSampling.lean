import OAI.GroupTheory.PolycyclicRecognition.Analysis.UniformProfileConcentration

namespace OAI

/-! # Independent suffix laws carried by the permitted boxes -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Sequential concentration for every permitted deterministic suffix
implies concentration for any independent laws carried by those sets. -/
theorem independent_supported_bad_probability_tendsto_zero
    {A K : ℕ → Type*} [∀ n, MeasurableSpace (A n)] [∀ n, MeasurableSpace (K n)]
    (μ : ∀ n, ProbabilityMeasure (A n)) (ν : ∀ n, ProbabilityMeasure (K n))
    (D : ∀ n, Set (K n)) (hne : ∀ n, (D n).Nonempty)
    (hcarried : ∀ n, ∀ᵐ k ∂(ν n : Measure (K n)), k ∈ D n)
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
    filter_upwards [hb] with n hn
    apply lt_of_le_of_lt _ hdc
    rw [Measure.prod_apply_symm (hB n)]
    calc
      _ ≤ ∫⁻ _, d ∂(ν n : Measure (K n)) := by
        apply lintegral_mono_ae
        filter_upwards [hcarried n] with k hk
        exact (hn ⟨k, hk⟩).le
      _ = d := by simp

end PolycyclicRecognition

end

end OAI
