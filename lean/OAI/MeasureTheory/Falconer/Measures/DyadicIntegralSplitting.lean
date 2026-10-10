import OAI.MeasureTheory.Falconer.Estimates.SpatialAnchorMasks
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem DyadicSquare.biUnion_descendants (Q : DyadicSquare) (hQ : 0 < Q.side)
    (n : ℕ) : (⋃ P ∈ dyadicPaths n, (Q.descendant P).carrier) = Q.carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨P, _, hx⟩ := mem_iUnion₂.mp hx
    exact Q.descendant_subset hQ P hx
  · intro hx
    obtain ⟨P, hP, hxP⟩ := Q.mem_descendant_at_depth n hx
    exact mem_iUnion₂.mpr ⟨P, hP, hxP⟩

theorem DyadicSquare.integral_split (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) (f : Plane → ℂ)
    (hf : IntegrableOn f Q.carrier ρ) :
    (∫ x in Q.carrier, f x ∂ρ) =
      ∑ P ∈ dyadicPaths n, ∫ x in (Q.descendant P).carrier, f x ∂ρ := by
  rw [← Q.biUnion_descendants hQ n]
  apply integral_biUnion_finset
  · exact fun P _ => (Q.descendant P).measurable
  · intro P hP S hS hne
    exact Q.descendants_disjoint hQ
      (((mem_dyadicPaths n P).mp hP).trans ((mem_dyadicPaths n S).mp hS).symm) hne
  · exact fun P _ => hf.mono_set (Q.descendant_subset hQ P)

theorem DyadicSquare.integral_split_occupied (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) (f : Plane → ℂ)
    (hf : IntegrableOn f Q.carrier ρ) :
    (∫ x in Q.carrier, f x ∂ρ) =
      ∑ P ∈ occupiedAnchorPaths Q ρ n, ∫ x in (Q.descendant P).carrier, f x ∂ρ := by
  classical
  rw [Q.integral_split hQ ρ n f hf]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro P hP hnot
  have hz : ρ (Q.descendant P).carrier = 0 := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hP, bot_lt_iff_ne_bot.mpr hne⟩)
  rw [Measure.restrict_eq_zero.mpr hz, integral_zero_measure]

theorem DyadicSquare.mass_split_occupied (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) :
    ρ Q.carrier = ∑ P ∈ occupiedAnchorPaths Q ρ n, ρ (Q.descendant P).carrier := by
  classical
  have hall : ρ Q.carrier = ∑ P ∈ dyadicPaths n, ρ (Q.descendant P).carrier := by
    rw [← Q.biUnion_descendants hQ n]
    apply measure_biUnion_finset
    · intro P hP S hS hne
      exact Q.descendants_disjoint hQ
        (((mem_dyadicPaths n P).mp hP).trans ((mem_dyadicPaths n S).mp hS).symm) hne
    · exact fun P _ => (Q.descendant P).measurable
  rw [hall]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro P hP hnot
  by_contra hne
  exact hnot (Finset.mem_filter.mpr ⟨hP, bot_lt_iff_ne_bot.mpr hne⟩)

theorem DyadicSquare.normalized_mass_split (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (n : ℕ) (M : ℝ) :
    (∑ P ∈ occupiedAnchorPaths Q ρ n, (ρ (Q.descendant P).carrier).toReal / M) =
      (ρ Q.carrier).toReal / M := by
  rw [← Finset.sum_div, Q.mass_split_occupied hQ ρ n, ENNReal.toReal_sum]
  exact fun P _ => measure_ne_top ρ _

end PlanarFalconer

end OAI
