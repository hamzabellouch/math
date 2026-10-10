import OAI.MeasureTheory.Falconer.Estimates.AllDimensionalRegularizationLabels
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

/-!
# Regularization classes on the original all-dimensional dyadic tree

Classes are literal disjoint unions of half-open leaves. The measure
identities and the discarded mass bounds hold for the original law.
-/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def leafUnion (Q : DyadicCube d) (L : Finset (CellPath d)) : Set (Space d) :=
  ⋃ p ∈ L, (Q.descendant p).carrier

theorem leafUnion_measurable (Q : DyadicCube d) (L : Finset (CellPath d)) :
    MeasurableSet (leafUnion Q L) :=
  Finset.measurableSet_biUnion _ (fun p _ => (Q.descendant p).measurable)

theorem leafUnion_subset (Q : DyadicCube d) (_hQ : 0 < Q.side)
    (L : Finset (CellPath d)) : leafUnion Q L ⊆ Q.carrier := by
  intro z hz
  obtain ⟨p,_,hp⟩ := mem_iUnion₂.mp hz
  exact Q.descendant_subset p hp

theorem leafUnion_mono (Q : DyadicCube d) {L T : Finset (CellPath d)}
    (h : L ⊆ T) : leafUnion Q L ⊆ leafUnion Q T := by
  intro z hz
  obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
  exact mem_iUnion₂.mpr ⟨p,h hp,hz⟩

theorem leafUnion_all (Q : DyadicCube d) (hQ : 0 < Q.side) (N : ℕ) :
    leafUnion Q (cubePaths d N) = Q.carrier := by
  apply Subset.antisymm (leafUnion_subset Q hQ _)
  intro z hz
  obtain ⟨p,hp,hz⟩ := Q.mem_descendant_at_depth N hz
  exact mem_iUnion₂.mpr ⟨p,hp,hz⟩

theorem leafUnion_disjoint (Q : DyadicCube d) (_hQ : 0 < Q.side) {N : ℕ}
    {L T : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (hT : T ⊆ cubePaths d N) (h : Disjoint L T) :
    Disjoint (leafUnion Q L) (leafUnion Q T) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨p,hp,hzp⟩ := mem_iUnion₂.mp hz
  obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz'
  have hne : p ≠ q := by
    intro he; subst q; exact Finset.disjoint_left.mp h hp hq
  exact Set.disjoint_left.mp (Q.descendants_disjoint
    ((mem_cubePaths _ _ _).mp (hL hp) |>.trans ((mem_cubePaths _ _ _).mp (hT hq)).symm)
    hne) hzp hzq

theorem measure_leafUnion (Q : DyadicCube d) (_hQ : 0 < Q.side) (μ : Measure (Space d))
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) :
    μ (leafUnion Q L) = ∑ p ∈ L, μ (Q.descendant p).carrier := by
  apply measure_biUnion_finset
  · intro p hp q hq hne
    exact Q.descendants_disjoint
      (((mem_cubePaths _ _ _).mp (hL hp)).trans ((mem_cubePaths _ _ _).mp (hL hq)).symm)
      hne
  · intro p _; exact (Q.descendant p).measurable

noncomputable def retainedLeaves (Q : DyadicCube d) (μ : Measure (Space d)) (N : ℕ)
    (t : ℝ≥0∞) : Finset (CellPath d) := by
  classical
  exact (cubePaths d N).filter fun p => t ≤ μ (Q.descendant p).carrier

theorem discarded_leaves_mass (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N : ℕ) (t : ℝ≥0∞) :
    μ (leafUnion Q (cubePaths d N \ retainedLeaves Q μ N t)) ≤ (2 : ℝ≥0∞)^(d*N) * t := by
  classical
  rw [measure_leafUnion Q hQ μ Finset.sdiff_subset]
  calc
    _ ≤ ∑ _p ∈ cubePaths d N \ retainedLeaves Q μ N t, t := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_sdiff.mp hp
      have : ¬ t ≤ μ (Q.descendant p).carrier := by
        intro ht
        exact hp'.2 (Finset.mem_filter.mpr ⟨hp'.1,ht⟩)
      exact (lt_of_not_ge this).le
    _ ≤ (2 : ℝ≥0∞)^(d*N) * t := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_left
      exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq (card_cubePaths d N))

noncomputable def classLeaves (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) (T : List ℕ) : Finset (CellPath d) := by
  classical
  exact L.filter fun p => f p = T

noncomputable def classMeasure (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ) :
    Measure (Space d) := μ.restrict (leafUnion Q (classLeaves L f T))

theorem classLeaves_disjoint (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) {T U : List ℕ} (h : T ≠ U) :
    Disjoint (classLeaves L f T) (classLeaves L f U) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact h ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)

theorem leafUnion_classes (Q : DyadicCube d) (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) :
    (⋃ T ∈ L.image f, leafUnion Q (classLeaves L f T)) = leafUnion Q L := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨T,_,hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨p,(Finset.mem_filter.mp hp).1,hz⟩
  · intro hz
    obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨f p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      mem_iUnion₂.mpr ⟨p,by simp [classLeaves,hp],hz⟩⟩

theorem class_mass_sum (Q : DyadicCube d) (hQ : 0 < Q.side) (μ : Measure (Space d))
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (f : CellPath d → List ℕ) :
    (∑ T ∈ L.image f, classMeasure Q μ L f T univ) = μ (leafUnion Q L) := by
  classical
  simp only [classMeasure, Measure.restrict_apply_univ]
  rw [← leafUnion_classes Q L f]
  symm
  apply measure_biUnion_finset
  · intro T _ U _ hne
    exact leafUnion_disjoint Q hQ (fun _ hp => hL (Finset.mem_filter.mp hp).1)
      (fun _ hp => hL (Finset.mem_filter.mp hp).1) (classLeaves_disjoint L f hne)
  · intro T _; exact leafUnion_measurable Q _

theorem discarded_classes_mass (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ)
    (t : ℝ≥0∞) :
    μ (⋃ T ∈ (L.image f).filter (fun T => classMeasure Q μ L f T univ < t),
      leafUnion Q (classLeaves L f T)) ≤ ((L.image f).card : ℝ≥0∞) * t := by
  classical
  calc
    _ ≤ ∑ T ∈ (L.image f).filter (fun T => classMeasure Q μ L f T univ < t),
        μ (leafUnion Q (classLeaves L f T)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _T ∈ (L.image f).filter (fun T => classMeasure Q μ L f T univ < t), t := by
      apply Finset.sum_le_sum
      intro T hT
      simpa only [classMeasure, Measure.restrict_apply_univ] using (Finset.mem_filter.mp hT).2.le
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_left
      exact_mod_cast (Finset.card_filter_le (s := L.image f)
        (fun T => classMeasure Q μ L f T univ < t))

noncomputable def normalizedClass (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ) :
    Measure (Space d) := (classMeasure Q μ L f T univ)⁻¹ • classMeasure Q μ L f T

theorem normalizedClass_probability (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) (T : List ℕ)
    (h : classMeasure Q μ L f T univ ≠ 0) :
    IsProbabilityMeasure (normalizedClass Q μ L f T) := by
  constructor
  simp only [normalizedClass, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel h
  simp only [classMeasure, Measure.restrict_apply_univ]
  exact measure_ne_top _ _

theorem normalizedClass_apply (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ)
    (S : Set (Space d)) :
    normalizedClass Q μ L f T S =
      (μ (leafUnion Q (classLeaves L f T)))⁻¹ *
        μ (S ∩ leafUnion Q (classLeaves L f T)) := by
  simp only [normalizedClass, classMeasure, univ_inter,
    Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (leafUnion_measurable Q _)]

end Falconer.Regularization

end OAI
