import Mathlib

namespace OAI

universe uX uI

open Filter Topology

noncomputable section
namespace Problem326

/-- Compactness upgrades a strict sequential activity bound to a uniform
small-parameter bound. No continuity of the activity predicate is needed. -/
theorem uniform_activity_of_sequential_bound
    {X : Type uX} [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set X} (hK : IsCompact K) (active : ℝ → X → Prop)
    (error : X → ℝ) (herror : Continuous error) (bound : ℝ)
    (hseq : ∀ (h : ℕ → ℝ) (p : ℕ → X) (p₀ : X),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      p₀ ∈ K → Tendsto p atTop (𝓝 p₀) →
      (∀ n, active (h n) (p n)) → error p₀ < bound) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ p ∈ K, active h p → error p < bound := by
  by_contra hnot
  push Not at hnot
  have hwitness : ∀ n : ℕ, ∃ h : ℝ, 0 < h ∧ h < 1 / ((n : ℝ) + 1) ∧
      ∃ p ∈ K, active h p ∧ bound ≤ error p := by
    intro n
    exact hnot (1 / ((n : ℝ) + 1)) (by positivity)
  choose h hhpos hhsmall p hpK hpactive hperror using hwitness
  have hhlim : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => (hhpos n).le) (fun n => (hhsmall n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p₀, hp₀, φ, hφ, hpφ⟩ := hK.tendsto_subseq hpK
  have hstrict : error p₀ < bound := hseq (h ∘ φ) (p ∘ φ) p₀
    (fun n => hhpos (φ n)) (hhlim.comp hφ.tendsto_atTop) hp₀ hpφ
    (fun n => hpactive (φ n))
  have hweak : bound ≤ error p₀ := ge_of_tendsto'
    ((herror.tendsto p₀).comp hpφ) (fun n => hperror (φ n))
  exact (not_lt_of_ge hweak) hstrict

/-- The uniform activity bound for finitely many labels. The error tolerance
may depend arbitrarily on the label; no regularity in that dependence is used. -/
theorem finite_uniform_activity_of_sequential_bound
    {X : Type uX} [TopologicalSpace X] [FirstCountableTopology X]
    {I : Type uI} [Finite I] {K : Set X} (hK : IsCompact K)
    (active : ℝ → X → I → Prop) (error : I → X → ℝ)
    (herror : ∀ i, Continuous (error i)) (bound : I → ℝ)
    (hseq : ∀ (i : I) (h : ℕ → ℝ) (p : ℕ → X) (p₀ : X),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      p₀ ∈ K → Tendsto p atTop (𝓝 p₀) →
      (∀ n, active (h n) (p n) i) → error i p₀ < bound i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ p ∈ K, ∀ i, active h p i → error i p < bound i := by
  have hev : ∀ i : I, ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ∀ p ∈ K, active h p i → error i p < bound i := by
    intro i
    obtain ⟨δ, hδ, hδprop⟩ := uniform_activity_of_sequential_bound hK
      (fun h p => active h p i) (error i) (herror i) (bound i) (hseq i)
    apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
    exact ⟨δ, hδ, fun h hh => hδprop h hh.1 hh.2⟩
  have hevall := Filter.eventually_all.mpr hev
  obtain ⟨δ, hδ, hδprop⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevall
  refine ⟨δ, hδ, ?_⟩
  intro h hhpos hhsmall p hp i
  exact hδprop ⟨hhpos, hhsmall⟩ i p hp

end Problem326

end

end OAI
