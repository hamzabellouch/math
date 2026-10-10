import OAI.MeasureTheory.Falconer.Measures.DyadicIntegralSplitting

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

 theorem DyadicSquare.measure_split_occupied (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) :
    ρ.restrict Q.carrier =
      ∑ P ∈ occupiedAnchorPaths Q ρ n, ρ.restrict (Q.descendant P).carrier := by
  classical
  have hall : ρ.restrict Q.carrier =
      ∑ P ∈ dyadicPaths n, ρ.restrict (Q.descendant P).carrier := by
    rw [← Q.biUnion_descendants hQ n]
    rw [Measure.restrict_biUnion_finset]
    · rw [Measure.sum_fintype]
      exact Finset.sum_coe_sort (dyadicPaths n) (fun P => ρ.restrict (Q.descendant P).carrier)
    · intro P hP S hS hne
      exact Q.descendants_disjoint hQ
        (((mem_dyadicPaths n P).mp hP).trans ((mem_dyadicPaths n S).mp hS).symm) hne
    · exact fun P => (Q.descendant P).measurable
  rw [hall]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro P hP hnot
  apply Measure.restrict_eq_zero.mpr
  by_contra hne
  exact hnot (Finset.mem_filter.mpr ⟨hP,bot_lt_iff_ne_bot.mpr hne⟩)

 theorem occupied_absolute_measure_sum (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (A : CellPath) (n : ℕ) :
    (∑ P ∈ (occupiedAnchorPaths (Q.descendant A) ρ n).image (fun c => A++c),
      ρ.restrict (Q.descendant P).carrier) = ρ.restrict (Q.descendant A).carrier := by
  classical
  rw [Finset.sum_image (fun _ _ _ _ he => List.append_cancel_left he)]
  simp only [DyadicSquare.descendant_append]
  exact ((Q.descendant A).measure_split_occupied (Q.descendant_side_pos hQ A) ρ n).symm

end PlanarFalconer

end OAI
