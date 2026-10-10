import OAI.Analysis.CircleDomains.Topology.PathImageCount
import OAI.Analysis.CircleDomains.Probability.CompactArcLaw

namespace OAI

/-! Distinct intersections decrease under subarc selection. Conditioning
on a compact family of mass at least one half costs at most a factor two. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem pathImageCount_mono_range (H : Set X) {α γ : C(PathTime, X)}
    (h : range α ⊆ range γ) : pathImageCount H α ≤ pathImageCount H γ := by
  unfold pathImageCount
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ range α ∩ H
  · have hy : x ∈ range γ ∩ H := ⟨h hx.1, hx.2⟩
    simp only [hx, hy, ite_true, le_refl]
  · simp only [hx, ite_false, zero_le]

theorem pathImageCount_le_timeCount (H : Set X) (γ : C(PathTime, X)) :
    pathImageCount H γ ≤ timeCount {p : C(PathTime, X) × PathTime | p.1 p.2 ∈ H} γ := by
  rw [pathImageCount_eq_iSup]
  apply iSup_le
  intro n
  split
  · rename_i hn
    obtain ⟨t, ht, hH⟩ := hn
    have hti : Injective t := fun i j hij => ht (congrArg γ hij)
    rw [timeCount_eq_iSup]
    exact (ite_eq_left (show γ ∈ timeWitnessSet
      {p : C(PathTime, X) × PathTime | p.1 p.2 ∈ H} n from ⟨t, hti, hH⟩)).symm.le.trans
        (le_iSup (fun k : ℕ => if γ ∈ timeWitnessSet
          {p : C(PathTime, X) × PathTime | p.1 p.2 ∈ H} k then (k : ℝ≥0∞) else 0) n)
  · exact bot_le

theorem pathImageCount_eq_timeCount_of_injective (H : Set X)
    (γ : C(PathTime, X)) (hγ : Injective γ) :
    pathImageCount H γ = timeCount {p : C(PathTime, X) × PathTime | p.1 p.2 ∈ H} γ := by
  apply le_antisymm (pathImageCount_le_timeCount H γ)
  rw [timeCount_eq_iSup]
  apply iSup_le
  intro n
  split
  · rename_i hn
    obtain ⟨t, ht, hH⟩ := hn
    rw [pathImageCount_eq_iSup]
    exact (ite_eq_left (show γ ∈ imageHitAtLeast H n from ⟨t, hγ.comp ht, hH⟩)).symm.le.trans
      (le_iSup (fun k : ℕ => if γ ∈ imageHitAtLeast H k then (k : ℝ≥0∞) else 0) n)
  · exact bot_le

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

/-- The actual measurable selection and domination data retained by compact
terminal subarc conditioning. -/
def IsSubarcLawReduction
    (μ η : ProbabilityMeasure C(PathTime, X)) : Prop :=
  ∃ f : C(PathTime, X) → C(PathTime, X),
    AEMeasurable f (μ : Measure C(PathTime, X)) ∧
    (∀ᵐ γ ∂(μ : Measure C(PathTime, X)), range (f γ) ⊆ range γ) ∧
    (η : Measure C(PathTime, X)) ≤ (2 : ℝ≥0∞) • (μ.map f : Measure C(PathTime, X))

theorem mean_subarc_intersections_le
    (μ η : ProbabilityMeasure C(PathTime, X)) (f : C(PathTime, X) → C(PathTime, X))
    (hf : AEMeasurable f (μ : Measure C(PathTime, X)))
    (hs : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), range (f γ) ⊆ range γ)
    (hη : (η : Measure C(PathTime, X)) ≤ (2 : ℝ≥0∞) • (μ.map f : Measure C(PathTime, X)))
    {H : Set X} (hH : IsClosed H) :
    (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, X))) ≤
      2 * ∫⁻ γ, pathImageCount H γ ∂(μ : Measure C(PathTime, X)) := by
  calc
    _ ≤ ∫⁻ α, pathImageCount H α ∂((2 : ℝ≥0∞) • (μ.map f : Measure C(PathTime, X))) :=
      lintegral_mono' hη le_rfl
    _ = 2 * ∫⁻ γ, pathImageCount H (f γ) ∂(μ : Measure C(PathTime, X)) := by
      rw [lintegral_smul_measure, ProbabilityMeasure.toMeasure_map,
        lintegral_map' (measurable_pathImageCount hH).aemeasurable hf]
      rfl
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_ae (hs.mono fun _ h => pathImageCount_mono_range H h))

theorem finite_mean_subarc_intersections
    (μ η : ProbabilityMeasure C(PathTime, X)) (f : C(PathTime, X) → C(PathTime, X))
    (hf : AEMeasurable f (μ : Measure C(PathTime, X)))
    (hs : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), range (f γ) ⊆ range γ)
    (hη : (η : Measure C(PathTime, X)) ≤ (2 : ℝ≥0∞) • (μ.map f : Measure C(PathTime, X)))
    {H : Set X} (hH : IsClosed H)
    (hfin : (∫⁻ γ, pathImageCount H γ ∂(μ : Measure C(PathTime, X))) < ∞) :
    (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, X))) < ∞ :=
  (mean_subarc_intersections_le μ η f hf hs hη hH).trans_lt
    (ENNReal.mul_lt_top (by norm_num) hfin)

end CircleDomainRigidity

end

end OAI
