import OAI.MeasureTheory.Falconer.Estimates.ComparableBands
import OAI.MeasureTheory.Falconer.Measures.FarOriginalSupport
import OAI.MeasureTheory.Falconer.Estimates.NoncomparableOriginalPointwise

namespace OAI

/-! # The two noncomparable pieces and finite comparable bands -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)

def leftNoncomparableFar (d a h : ℕ) :
    Set ((Space d × Space d) × (Space d × Space d)) :=
  farDisplacementRegion d a h ∩ {z | 2*dist z.2.1 z.2.2 < dist z.1.1 z.1.2}

def rightNoncomparableFar (d a h : ℕ) :
    Set ((Space d × Space d) × (Space d × Space d)) :=
  farDisplacementRegion d a h ∩ {z | 2*dist z.1.1 z.1.2 < dist z.2.1 z.2.2}

theorem leftNoncomparableFar_measurable (d a h : ℕ) :
    MeasurableSet (leftNoncomparableFar d a h) := by
  apply (farDisplacementRegion_measurable d a h).inter
  exact measurableSet_lt
    (show Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      2*dist z.2.1 z.2.2) by fun_prop)
    (by fun_prop)

theorem rightNoncomparableFar_measurable (d a h : ℕ) :
    MeasurableSet (rightNoncomparableFar d a h) := by
  apply (farDisplacementRegion_measurable d a h).inter
  exact measurableSet_lt
    (show Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      2*dist z.1.1 z.1.2) by fun_prop)
    (by fun_prop)

theorem farDisplacementRegion_subset_split (d a h : ℕ) :
    farDisplacementRegion d a h ⊆
      (leftNoncomparableFar d a h ∪ rightNoncomparableFar d a h) ∪ comparableFarRegion d a h := by
  intro z hz
  by_cases hl : 2*dist z.2.1 z.2.2 < dist z.1.1 z.1.2
  · exact Or.inl (Or.inl ⟨hz,hl⟩)
  by_cases hr : 2*dist z.1.1 z.1.2 < dist z.2.1 z.2.2
  · exact Or.inl (Or.inr ⟨hz,hr⟩)
  apply Or.inr
  refine ⟨hz.1,hz.2,max_le ?_ (le_of_not_gt hr),max_le (le_of_not_gt hl) ?_⟩
  · have hd : 0 ≤ dist z.1.1 z.1.2 := dist_nonneg
    linarith
  · have hd : 0 ≤ dist z.2.1 z.2.2 := dist_nonneg
    linarith

theorem lintegral_far_split_bands (d a h : ℕ)
    (μ : Measure ((Space d × Space d) × (Space d × Space d)))
    (F : ((Space d × Space d) × (Space d × Space d)) → ℝ≥0∞) :
    (∫⁻ z in farDisplacementRegion d a h, F z ∂μ) ≤
      (∫⁻ z in leftNoncomparableFar d a h, F z ∂μ) +
      (∫⁻ z in rightNoncomparableFar d a h, F z ∂μ) +
      ∑ b ∈ Finset.Icc (a+9) (h+6),
        ∫⁻ z in comparableFarRegion d a h ∩ comparableLengthBand d b, F z ∂μ := by
  calc
    _ ≤ ∫⁻ z in (leftNoncomparableFar d a h ∪ rightNoncomparableFar d a h) ∪
        comparableFarRegion d a h, F z ∂μ :=
      lintegral_mono' (Measure.restrict_mono_set μ (farDisplacementRegion_subset_split d a h))
        (fun _ => le_rfl)
    _ ≤ (∫⁻ z in leftNoncomparableFar d a h ∪ rightNoncomparableFar d a h, F z ∂μ) +
        ∫⁻ z in comparableFarRegion d a h, F z ∂μ := lintegral_union_le _ _ _
    _ ≤ _ := add_le_add (lintegral_union_le _ _ _)
      (lintegral_comparable_bands_le d a h μ F (subset_refl _))

end Falconer

end OAI
