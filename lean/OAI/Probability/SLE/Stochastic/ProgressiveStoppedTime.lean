import OAI.Probability.SLE.Stochastic.ProgressiveRandomTime
import OAI.Probability.SLE.Stochastic.ShiftedStoppingFiltration

namespace OAI

/-! Stopped-value measurability for a progressive process with a merely
measurable target, in particular a measure-valued canonical mass. -/

noncomputable section
open Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped NNReal ENNReal

namespace MeasureTheory.IsProgressive
open scoped _root_.MeasureTheory _root_.MeasureTheory.IsProgressive

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
  {ℱ : _root_.MeasureTheory.Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → X}

lemma bounded_stopped_measurable (hN : _root_.MeasureTheory.IsProgressive ℱ N)
    (τ : Ω → ℝ≥0)
    (hτ : _root_.MeasureTheory.IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hH : ∀ ω, τ ω ≤ H) :
    Measurable[ℱ H] (fun ω => N (τ ω) ω) := by
  have htime : Measurable[ℱ H] τ := by
    have h := (hτ.measurable_of_le (fun ω => WithTop.coe_le_coe.mpr (hH ω))).untopA
    convert h using 1
    funext ω
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]
    rfl
  have hp : Measurable[ℱ H,Subtype.instMeasurableSpace.prod (ℱ H)]
      (fun ω => ((⟨τ ω,hH ω⟩ : Iic H),ω)) := by
    exact htime.subtype_mk.prodMk measurable_id
  exact (hN H).comp hp

lemma truncated_stopped_measurable (hN : _root_.MeasureTheory.IsProgressive ℱ N)
    (τ : Ω → ℝ≥0)
    (hτ : _root_.MeasureTheory.IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) (H : ℝ≥0) :
    Measurable[ℱ H] (fun ω => N (min (τ ω) H) ω) := by
  have hmin : _root_.MeasureTheory.IsStoppingTime ℱ (fun ω => ((min (τ ω) H : ℝ≥0) : WithTop ℝ≥0)) := by
    simpa only [WithTop.coe_min] using hτ.min_const H
  exact _root_.OAI.MeasureTheory.IsProgressive.bounded_stopped_measurable hN _ hmin H (fun _ => min_le_right _ _)

/-- This requires no topology on the target. -/
theorem stopped_time_measurable (hN : _root_.MeasureTheory.IsProgressive ℱ N)
    (τ : Ω → ℝ≥0)
    (hτ : _root_.MeasureTheory.IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace] (fun ω => N (τ ω) ω) := by
  have hslice (S : Set X) (hS : MeasurableSet S) (H : ℝ≥0) :
      MeasurableSet[ℱ H] ((fun ω => N (τ ω) ω) ⁻¹' S ∩ {ω | τ ω ≤ H}) := by
    have he : (fun ω => N (τ ω) ω) ⁻¹' S ∩ {ω | τ ω ≤ H} =
        (fun ω => N (min (τ ω) H) ω) ⁻¹' S ∩ {ω | τ ω ≤ H} := by
      ext ω
      simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq]
      constructor <;> rintro ⟨hω,ht⟩ <;> exact ⟨by simpa only [min_eq_left ht] using hω,ht⟩
    rw [he]
    exact ((_root_.OAI.MeasureTheory.IsProgressive.truncated_stopped_measurable hN τ hτ H) hS).inter (by simpa only [WithTop.coe_le_coe] using hτ H)
  intro S hS
  constructor
  · have he : (fun ω => N (τ ω) ω) ⁻¹' S =
        ⋃ n : ℕ, (fun ω => N (τ ω) ω) ⁻¹' S ∩ {ω | τ ω ≤ (n:ℝ≥0)} := by
      ext ω
      simp only [mem_preimage,mem_iUnion,mem_inter_iff,mem_ofPred_eq]
      constructor
      · intro hω
        obtain ⟨n,hn⟩ := exists_nat_ge (τ ω : ℝ)
        exact ⟨n,hω,by exact_mod_cast hn⟩
      · rintro ⟨n,hω,_⟩
        exact hω
    rw [he]
    exact MeasurableSet.iUnion (fun n => le_iSup ℱ (n:ℝ≥0) _ (hslice S hS n))
  · intro H
    simpa only [WithTop.coe_le_coe] using hslice S hS H

/-- The original measure-valued process evaluated after a finite stopping
time is adapted to the full shifted stopped-past filtration. -/
theorem shifted_adapted (hN : _root_.MeasureTheory.IsProgressive ℱ N)
    (τ : Ω → ℝ≥0)
    (hτ : _root_.MeasureTheory.IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    _root_.MeasureTheory.Adapted (SLEExactGauge.shiftedStoppingFiltration hτ)
      (fun t ω => N (τ ω+t) ω) := by
  intro t
  exact _root_.OAI.MeasureTheory.IsProgressive.stopped_time_measurable hN _ (SLEExactGauge.stopping_time_add_nnreal hτ t)

end MeasureTheory.IsProgressive

end

end OAI
