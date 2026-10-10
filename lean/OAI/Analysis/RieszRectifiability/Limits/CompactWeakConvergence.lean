import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.WeakRestriction

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction CompactlySupported

def CompactTestConvergence {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d)) : Prop :=
  ∀ f : C_c(Ambient d, ℝ), Tendsto (fun j => ∫ x, f x ∂μ j) atTop (𝓝 (∫ x, f x ∂ν))

def compactWeightedFiniteMeasure {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0)) : FiniteMeasure (Ambient d) := by
  refine ⟨μ.withDensity (fun x => (f x : ℝ≥0∞)), ?_⟩
  have hf : Integrable (fun x => (f x : ℝ)) μ :=
    (NNReal.continuous_coe.comp f.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_left (g := ((↑) : ℝ≥0 → ℝ)) rfl)
  simpa only [ENNReal.ofReal_coe_nnreal] using!
    isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral

theorem compactWeightedFiniteMeasure_integral {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0)) (g : Ambient d → ℝ) :
    (∫ x, g x ∂(compactWeightedFiniteMeasure μ f : Measure (Ambient d))) =
      ∫ x, (f x : ℝ) * g x ∂μ := by
  exact integral_withDensity_eq_integral_smul f.continuous.measurable g

theorem compactWeightedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (f : C_c(Ambient d, ℝ≥0)) :
    Tendsto (fun j => compactWeightedFiniteMeasure (μ j) f) atTop
      (𝓝 (compactWeightedFiniteMeasure ν f)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  let test : C_c(Ambient d, ℝ) :=
    ⟨⟨fun x => f.toReal x * g x, f.toReal.continuous.mul g.continuous⟩,
      f.toReal.hasCompactSupport.mul_right⟩
  have ht := hlocal test
  change Tendsto (fun j => ∫ x, f.toReal x * g x ∂μ j) atTop
    (𝓝 (∫ x, f.toReal x * g x ∂ν)) at ht
  simpa only [compactWeightedFiniteMeasure_integral,
    CompactlySupportedContinuousMap.toReal_apply] using! ht

theorem exists_compact_nonneg_cutoff {d : ℕ} (s : Set (Ambient d)) (hs : IsCompact s) :
    ∃ f : C_c(Ambient d, ℝ≥0), (∀ x ∈ s, f x = 1) ∧ ∀ x, f x ≤ 1 := by
  obtain ⟨g, hgs, _, hgc, hg⟩ :=
    exists_continuous_one_zero_of_isCompact hs isClosed_empty (disjoint_empty s)
  let g₀ : C_c(Ambient d, ℝ) := ⟨g, hgc⟩
  refine ⟨g₀.nnrealPart, ?_, ?_⟩
  · intro x hx
    change Real.toNNReal (g x) = 1
    rw [show g x = 1 from hgs hx]
    simp
  · intro x
    change Real.toNNReal (g x) ≤ 1
    simpa using! Real.toNNReal_le_toNNReal (hg x).2

theorem compactWeightedFiniteMeasure_restrict {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0))
    (s : Set (Ambient d)) (hs : MeasurableSet s) (hf : ∀ x ∈ s, f x = 1) :
    (compactWeightedFiniteMeasure μ f : Measure (Ambient d)).restrict s = μ.restrict s := by
  change (μ.withDensity (fun x => (f x : ℝ≥0∞))).restrict s = _
  rw [restrict_withDensity hs]
  calc
    _ = (μ.restrict s).withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      simp only [hf x hx, ENNReal.coe_one, Pi.one_apply]
    _ = _ := withDensity_one

theorem relativelyCompact_restrict_finite {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (s : Set (Ambient d)) (hc : IsCompact (closure s)) :
    IsFiniteMeasure (μ.restrict s) :=
  isFiniteMeasure_restrict.mpr (ne_of_lt ((measure_mono subset_closure).trans_lt hc.measure_lt_top))

def relativelyCompactFiniteMeasure {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (s : Set (Ambient d)) (hc : IsCompact (closure s)) :
    FiniteMeasure (Ambient d) := ⟨μ.restrict s, relativelyCompact_restrict_finite μ s hc⟩

theorem compactTestConvergence_restrict_tendsto {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (s : Set (Ambient d))
    (hs : MeasurableSet s) (hc : IsCompact (closure s))
    (hboundary : ν (frontier s) = 0) :
    Tendsto (fun j => relativelyCompactFiniteMeasure (μ j) s hc) atTop
      (𝓝 (relativelyCompactFiniteMeasure ν s hc)) := by
  obtain ⟨f, hf, _⟩ := exists_compact_nonneg_cutoff (closure s) hc
  have hf' : ∀ x ∈ s, f x = 1 := fun x hx => hf x (subset_closure hx)
  have hb : (compactWeightedFiniteMeasure ν f : Measure (Ambient d)) (frontier s) = 0 :=
    withDensity_absolutelyContinuous _ _ hboundary
  have h := restrictedFiniteMeasure_tendsto (fun j => compactWeightedFiniteMeasure (μ j) f)
    (compactWeightedFiniteMeasure ν f) (compactWeightedFiniteMeasure_tendsto μ ν hlocal f) s hs hb
  have heq : ∀ (ρ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ρ],
      restrictedFiniteMeasure (compactWeightedFiniteMeasure ρ f) s =
        relativelyCompactFiniteMeasure ρ s hc := by
    intro ρ _
    apply Subtype.ext
    exact compactWeightedFiniteMeasure_restrict ρ f s hs hf'
  simpa only [heq] using! h

end

end RieszRectifiability

end OAI
