import OAI.Analysis.CircleDomains.Selection.FiniteFreeCount
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import OAI.Analysis.CircleDomains.Probability.CircleNullImage

namespace OAI

/-! The single-level conclusions pass to each finite prior union, with
its actual product Haar law and the sum of the expected counts.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem pathImageCount_iUnion_le_sum {n : ℕ} (H : Fin n → Set X)
    (γ : C(PathTime, X)) :
    pathImageCount (⋃ i, H i) γ ≤ ∑ i, pathImageCount (H i) γ := by
  simpa only [pathImageCount_eq_encard, ENNReal.tsum_set_one, ← inter_iUnion] using
    (ENNReal.tsum_iUnion_le (fun _ : X => (1 : ℝ≥0∞)) (fun i => range γ ∩ H i))

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

theorem ae_finite_tuple_level_law {n : ℕ}
    (H : Fin n → Set (UnitAddCircle × X)) (hH : ∀ i, IsClosed (H i))
    (Free : Set X) {Z : Type*} [MeasurableSpace Z] (P : ProbabilityMeasure Z)
    (γmap : Z → C(PathTime, X)) (hγmap : Measurable γmap)
    (hgood : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ z, pathImageCount {x | (t, x) ∈ H i} (γmap z) ∂(P : Measure Z)) < ∞ ∧
      ∀ᵐ z ∂(P : Measure Z), ¬ ∃ x ∈ range (γmap z) ∩ Free, (t, x) ∈ H i) :
    ∀ᵐ t ∂(Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))),
      (∫⁻ z, pathImageCount (⋃ i, {x | (t i, x) ∈ H i}) (γmap z) ∂(P : Measure Z)) < ∞ ∧
      ∀ᵐ z ∂(P : Measure Z),
        ¬ ∃ x ∈ range (γmap z) ∩ Free, x ∈ ⋃ i, {x | (t i, x) ∈ H i} := by
  have hall : ∀ᵐ t ∂(Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))),
      ∀ i, (∫⁻ z, pathImageCount {x | (t i, x) ∈ H i} (γmap z) ∂(P : Measure Z)) < ∞ ∧
        ∀ᵐ z ∂(P : Measure Z), ¬ ∃ x ∈ range (γmap z) ∩ Free, (t i, x) ∈ H i :=
    ae_all_iff.mpr fun i => (measurePreserving_eval
      (fun _ : Fin n => (volume : Measure UnitAddCircle)) i).quasiMeasurePreserving.ae (hgood i)
  filter_upwards [hall] with t ht
  constructor
  · have hc (i : Fin n) : Measurable (fun z => pathImageCount {x | (t i, x) ∈ H i} (γmap z)) :=
      (measurable_pathImageCount ((hH i).preimage (continuous_const.prodMk continuous_id))).comp hγmap
    apply (show (∫⁻ z, pathImageCount (⋃ i, {x | (t i, x) ∈ H i}) (γmap z) ∂(P : Measure Z)) ≤
        ∑ i, ∫⁻ z, pathImageCount {x | (t i, x) ∈ H i} (γmap z) ∂(P : Measure Z) from ?_).trans_lt
      (ENNReal.sum_lt_top.mpr fun i _ => (ht i).1)
    calc
      _ ≤ ∫⁻ z, ∑ i, pathImageCount {x | (t i, x) ∈ H i} (γmap z) ∂(P : Measure Z) :=
        lintegral_mono fun z => pathImageCount_iUnion_le_sum _ (γmap z)
      _ = _ := lintegral_finsetSum _ (fun i _ => hc i)
  · filter_upwards [ae_all_iff.mpr (fun i => (ht i).2)] with z hz
    rintro ⟨x, hx, hmem⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
    exact hz i ⟨x, hx, hi⟩

end CircleDomainRigidity

end

end OAI
