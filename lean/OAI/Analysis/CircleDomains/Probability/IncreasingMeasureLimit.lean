import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.GiryMonad

namespace OAI

/-! Pointwise increasing limits of the finite-stage occupation measures. -/

open Set MeasureTheory Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem tsum_iSup_of_monotone (f : ℕ → ℕ → ℝ≥0∞) (hf : Monotone f) :
    (∑' i, ⨆ n, f n i) = ⨆ n, ∑' i, f n i := by
  simpa only [lintegral_count] using
    (lintegral_iSup (μ := Measure.count) (fun _ => measurable_of_countable _) hf)

variable {Y : Type*} [MeasurableSpace Y]

theorem increasingMeasureLimit_iUnion (μ : ℕ → Measure Y) (hμ : Monotone μ)
    {f : ℕ → Set Y} (hf : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    (⨆ n, μ n (⋃ i, f i)) = ∑' i, ⨆ n, μ n (f i) := by
  simp_rw [measure_iUnion hd hf]
  symm
  exact tsum_iSup_of_monotone (fun n i => μ n (f i)) (fun n m h i => hμ h (f i))

def increasingMeasureLimit (μ : ℕ → Measure Y) (hμ : Monotone μ) : Measure Y :=
  Measure.ofMeasurable (fun s _ => ⨆ n, μ n s) (by simp)
    (fun _ hf hd => increasingMeasureLimit_iUnion μ hμ hf hd)

theorem increasingMeasureLimit_apply (μ : ℕ → Measure Y) (hμ : Monotone μ)
    {s : Set Y} (hs : MeasurableSet s) :
    increasingMeasureLimit μ hμ s = ⨆ n, μ n s :=
  Measure.ofMeasurable_apply s hs

theorem le_increasingMeasureLimit (μ : ℕ → Measure Y) (hμ : Monotone μ) (n : ℕ) :
    μ n ≤ increasingMeasureLimit μ hμ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [increasingMeasureLimit_apply μ hμ hs]
  exact le_iSup (fun n => μ n s) n

theorem measurable_increasingMeasureLimit {Z : Type*} [MeasurableSpace Z]
    (μ : Z → ℕ → Measure Y) (hμ : ∀ z, Monotone (μ z))
    (hmeas : ∀ n, Measurable (fun z => μ z n)) :
    Measurable (fun z => increasingMeasureLimit (μ z) (hμ z)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [increasingMeasureLimit_apply _ _ hs]
  exact Measurable.iSup fun n => (Measure.measurable_coe hs).comp (hmeas n)

end CircleDomainRigidity

end

end OAI
