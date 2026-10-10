import OAI.MeasureTheory.Falconer.Recursion.BlockRegularization

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

noncomputable def retainedClassLabels (Q : DyadicSquare) (μ : Measure Plane)
    (N B : ℕ) (t : ℝ≥0∞) : Finset (List ℕ) := by
  classical
  let L := regularizationLeaves Q μ N
  let F := regularizationLabel Q μ N B
  exact (L.image F).filter fun T => t ≤ classMeasure Q μ L F T univ

noncomputable def retainedClassUnion (Q : DyadicSquare) (μ : Measure Plane)
    (N B : ℕ) (t : ℝ≥0∞) : Set Plane :=
  ⋃ T ∈ retainedClassLabels Q μ N B t,
    leafUnion Q (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T)

theorem retainedClassLabels_count (Q : DyadicSquare) (μ : Measure Plane)
    (N B : ℕ) (t : ℝ≥0∞) : (retainedClassLabels Q μ N B t).card ≤
      (2*N+1)^(N/B+1)*(4*N+1) := by
  exact (Finset.card_filter_le _ _).trans (regularization_label_count Q μ N B)

theorem retainedClass_mass_lower (Q : DyadicSquare) (μ : Measure Plane)
    {N B : ℕ} {t : ℝ≥0∞} {T : List ℕ} (hT : T ∈ retainedClassLabels Q μ N B t) :
    t ≤ classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T univ :=
  (Finset.mem_filter.mp hT).2

theorem retainedClassUnion_measurable (Q : DyadicSquare) (μ : Measure Plane)
    (N B : ℕ) (t : ℝ≥0∞) : MeasurableSet (retainedClassUnion Q μ N B t) :=
  Finset.measurableSet_biUnion _ (fun _ _ => leafUnion_measurable Q _)

theorem retainedClassUnion_mass (Q : DyadicSquare) (hQ : 0 < Q.side) (μ : Measure Plane)
    (N B : ℕ) (t : ℝ≥0∞) : μ (retainedClassUnion Q μ N B t) =
      ∑ T ∈ retainedClassLabels Q μ N B t,
        classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T univ := by
  classical
  simp only [classMeasure,Measure.restrict_apply_univ]
  apply measure_biUnion_finset
  · intro T _ U _ hne
    apply leafUnion_disjoint Q hQ (N := N)
    · exact fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    · exact fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    · exact classLeaves_disjoint _ _ hne
  · intro T _; exact leafUnion_measurable Q _

theorem retainedClass_mass_sum_le_one (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (N B : ℕ) (t : ℝ≥0∞) :
    (∑ T ∈ retainedClassLabels Q μ N B t,
      classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T univ) ≤ 1 := by
  rw [← retainedClassUnion_mass Q hQ μ N B t]
  exact prob_le_one

theorem retainedClass_discard_mass (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ : Measure Plane) (hcarry : μ Q.carrierᶜ = 0) (N B : ℕ) (t : ℝ≥0∞) :
    μ (retainedClassUnion Q μ N B t)ᶜ ≤
      (4:ℝ≥0∞)^N * ((2:ℝ≥0∞)^(4*N))⁻¹ +
      (((2*N+1)^(N/B+1)*(4*N+1):ℕ):ℝ≥0∞)*t := by
  classical
  let L := regularizationLeaves Q μ N
  let F := regularizationLabel Q μ N B
  let D := (L.image F).filter fun T => classMeasure Q μ L F T univ < t
  let bad := ⋃ T ∈ D, leafUnion Q (classLeaves L F T)
  have hcover : (retainedClassUnion Q μ N B t)ᶜ ⊆
      (leafUnion Q (dyadicPaths N \ L) ∪ bad) ∪ Q.carrierᶜ := by
    intro z hz
    by_cases hQz : z ∈ Q.carrier
    · obtain ⟨p,hp,hzp⟩ := Q.mem_descendant_at_depth N hQz
      by_cases hpL : p ∈ L
      · have hbad : classMeasure Q μ L F (F p) univ < t := by
          by_contra h
          apply hz
          exact mem_iUnion₂.mpr ⟨F p, Finset.mem_filter.mpr
            ⟨Finset.mem_image.mpr ⟨p,hpL,rfl⟩,not_lt.mp h⟩,
            mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hpL,rfl⟩,hzp⟩⟩
        exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨F p, Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨p,hpL,rfl⟩,hbad⟩,
          mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hpL,rfl⟩,hzp⟩⟩))
      · exact Or.inl (Or.inl (mem_iUnion₂.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hp,hpL⟩,hzp⟩))
    · exact Or.inr hQz
  calc
    _ ≤ μ ((leafUnion Q (dyadicPaths N \ L) ∪ bad) ∪ Q.carrierᶜ) := measure_mono hcover
    _ ≤ μ (leafUnion Q (dyadicPaths N \ L) ∪ bad) + μ Q.carrierᶜ := measure_union_le _ _
    _ = μ (leafUnion Q (dyadicPaths N \ L) ∪ bad) := by rw [hcarry,add_zero]
    _ ≤ μ (leafUnion Q (dyadicPaths N \ L)) + μ bad := measure_union_le _ _
    _ ≤ (4:ℝ≥0∞)^N * ((2:ℝ≥0∞)^(4*N))⁻¹ + ((L.image F).card:ℝ≥0∞)*t :=
      add_le_add (discarded_leaves_mass Q hQ μ N _) (discarded_classes_mass Q μ L F t)
    _ ≤ _ := by
      apply add_le_add_right
      apply mul_le_mul_left
      exact_mod_cast regularization_label_count Q μ N B

end PlanarFalconer

end OAI
