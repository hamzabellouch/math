import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Measures.PathIndex2

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}
noncomputable def leafUnion (L : Finset ((CellPath d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ p ∈ L, (treeCell p)

theorem leafUnion_measurable (L : Finset ((CellPath d))) :
    MeasurableSet (leafUnion L) :=
  Finset.measurableSet_biUnion _ (fun p _ => (measurableSet_treeCell p))

theorem leafUnion_mono {L T : Finset ((CellPath d))}
    (h : L ⊆ T) : leafUnion L ⊆ leafUnion T := by
  intro z hz
  obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
  exact mem_iUnion₂.mpr ⟨p,h hp,hz⟩

theorem leafUnion_disjoint {N : ℕ}
    {L T : Finset ((CellPath d))} (hL : L ⊆ dyadicPaths N)
    (hT : T ⊆ dyadicPaths N) (h : Disjoint L T) :
    Disjoint (leafUnion L) (leafUnion T) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨p,hp,hzp⟩ := mem_iUnion₂.mp hz
  obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz'
  have hne : p ≠ q := by
    intro he; subst q; exact Finset.disjoint_left.mp h hp hq
  exact Set.disjoint_left.mp (treeCell_disjoint
    ((mem_dyadicPaths _ _).mp (hL hp) |>.trans ((mem_dyadicPaths _ _).mp (hT hq)).symm)
    hne) hzp hzq

theorem measure_leafUnion (μ : Measure (EuclideanSpace ℝ (Fin d)))
    {N : ℕ} {L : Finset ((CellPath d))} (hL : L ⊆ dyadicPaths N) :
    μ (leafUnion L) = ∑ p ∈ L, μ (treeCell p) := by
  apply measure_biUnion_finset
  · intro p hp q hq hne
    exact treeCell_disjoint
      (((mem_dyadicPaths _ _).mp (hL hp)).trans ((mem_dyadicPaths _ _).mp (hL hq)).symm)
      hne
  · intro p _; exact (measurableSet_treeCell p)

noncomputable def retainedLeaves (μ : Measure (EuclideanSpace ℝ (Fin d))) (N : ℕ)
    (t : ℝ≥0∞) : Finset ((CellPath d)) := by
  classical
  exact (dyadicPaths N).filter fun p => t ≤ μ (treeCell p)

theorem discarded_leaves_mass (μ : Measure (EuclideanSpace ℝ (Fin d))) (N : ℕ) (t : ℝ≥0∞) :
    μ (leafUnion (dyadicPaths N \ retainedLeaves μ N t)) ≤ (2 : ℝ≥0∞)^(d*N) * t := by
  classical
  rw [measure_leafUnion μ Finset.sdiff_subset]
  calc
    _ ≤ ∑ _p ∈ dyadicPaths N \ retainedLeaves μ N t, t := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_sdiff.mp hp
      have : ¬ t ≤ μ (treeCell p) := by
        intro ht
        exact hp'.2 (Finset.mem_filter.mpr ⟨hp'.1,ht⟩)
      exact (lt_of_not_ge this).le
    _ ≤ (2 : ℝ≥0∞)^(d*N) * t := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_left
      exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans (by simpa only [← pow_mul,Nat.mul_comm] using dyadicPaths_card_le (d := d) N)

noncomputable def classMeasure (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (L : Finset ((CellPath d))) (f : (CellPath d) → List ℕ) (T : List ℕ) :
    Measure (EuclideanSpace ℝ (Fin d)) := μ.restrict (leafUnion (classLeaves L f T))

theorem classLeaves_disjoint (L : Finset ((CellPath d)))
    (f : (CellPath d) → List ℕ) {T U : List ℕ} (h : T ≠ U) :
    Disjoint (classLeaves L f T) (classLeaves L f U) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact h ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)

theorem leafUnion_classes (L : Finset ((CellPath d)))
    (f : (CellPath d) → List ℕ) :
    (⋃ T ∈ L.image f, leafUnion (classLeaves L f T)) = leafUnion L := by
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

theorem class_mass_sum (μ : Measure (EuclideanSpace ℝ (Fin d)))
    {N : ℕ} {L : Finset ((CellPath d))} (hL : L ⊆ dyadicPaths N)
    (f : (CellPath d) → List ℕ) :
    (∑ T ∈ L.image f, classMeasure μ L f T univ) = μ (leafUnion L) := by
  classical
  simp only [classMeasure, Measure.restrict_apply_univ]
  rw [← leafUnion_classes L f]
  symm
  apply measure_biUnion_finset
  · intro T _ U _ hne
    exact leafUnion_disjoint (fun _ hp => hL (Finset.mem_filter.mp hp).1)
      (fun _ hp => hL (Finset.mem_filter.mp hp).1) (classLeaves_disjoint L f hne)
  · intro T _; exact leafUnion_measurable _

theorem discarded_classes_mass (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (L : Finset ((CellPath d))) (f : (CellPath d) → List ℕ)
    (t : ℝ≥0∞) :
    μ (⋃ T ∈ (L.image f).filter (fun T => classMeasure μ L f T univ < t),
      leafUnion (classLeaves L f T)) ≤ ((L.image f).card : ℝ≥0∞) * t := by
  classical
  calc
    _ ≤ ∑ T ∈ (L.image f).filter (fun T => classMeasure μ L f T univ < t),
        μ (leafUnion (classLeaves L f T)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _T ∈ (L.image f).filter (fun T => classMeasure μ L f T univ < t), t := by
      apply Finset.sum_le_sum
      intro T hT
      simpa only [classMeasure, Measure.restrict_apply_univ] using (Finset.mem_filter.mp hT).2.le
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_left
      exact_mod_cast (Finset.card_filter_le (s := L.image f)
        (fun T => classMeasure μ L f T univ < t))

noncomputable def normalizedClass (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (L : Finset ((CellPath d))) (f : (CellPath d) → List ℕ) (T : List ℕ) :
    Measure (EuclideanSpace ℝ (Fin d)) := (classMeasure μ L f T univ)⁻¹ • classMeasure μ L f T

theorem normalizedClass_probability (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (L : Finset ((CellPath d)))
    (f : (CellPath d) → List ℕ) (T : List ℕ)
    (h : classMeasure μ L f T univ ≠ 0) :
    IsProbabilityMeasure (normalizedClass μ L f T) := by
  constructor
  simp only [normalizedClass, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel h
  simp only [classMeasure, Measure.restrict_apply_univ]
  exact measure_ne_top _ _

theorem normalizedClass_apply (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (L : Finset ((CellPath d))) (f : (CellPath d) → List ℕ) (T : List ℕ)
    (S : Set (EuclideanSpace ℝ (Fin d))) :
    normalizedClass μ L f T S =
      (μ (leafUnion (classLeaves L f T)))⁻¹ *
        μ (S ∩ leafUnion (classLeaves L f T)) := by
  simp only [normalizedClass, classMeasure,
    Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (leafUnion_measurable _), univ_inter]

theorem leafUnion_inter_prefix {N a : ℕ} (ha : a ≤ N) {C : Finset (CellPath d)} (hC : C ⊆ dyadicPaths N)
    {P : (CellPath d)} (hP : P.length = a) :
    (treeCell P) ∩ leafUnion C = leafUnion (prefixFiber C a P) := by
  classical
  ext z
  constructor
  · rintro ⟨hzP,hzC⟩
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hzC
    have hqN := (mem_dyadicPaths _ _).mp (hC hq)
    have hlen : (q.take a).length = P.length := by simp [List.length_take,hqN,ha,hP]
    have he : q.take a = P := by
      by_contra hne
      exact Set.disjoint_left.mp (treeCell_disjoint hlen hne)
        (treeCell_subset_take q a hzq) hzP
    exact mem_iUnion₂.mpr ⟨q,by simp [prefixFiber,hq,he],hzq⟩
  · intro hz
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
    obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
    refine ⟨?_,mem_iUnion₂.mpr ⟨q,hq,hzq⟩⟩
    rw [← he]
    exact treeCell_subset_take q a hzq

theorem restriction_prefix_mass (μ : Measure (EuclideanSpace ℝ (Fin d)))
    {N a : ℕ} (ha : a ≤ N) {C : Finset (CellPath d)} (hC : C ⊆ dyadicPaths N)
    {P : (CellPath d)} (hP : P.length = a) :
    (μ.restrict (leafUnion C)) (treeCell P) =
      ∑ q ∈ prefixFiber C a P, μ (treeCell q) := by
  rw [Measure.restrict_apply (measurableSet_treeCell P),
    leafUnion_inter_prefix ha hC hP]
  exact measure_leafUnion μ (fun q hq => hC (Finset.mem_filter.mp hq).1)

theorem restriction_prefix_mass_real (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    {N a : ℕ} (ha : a ≤ N) {C : Finset (CellPath d)} (hC : C ⊆ dyadicPaths N)
    {P : (CellPath d)} (hP : P.length = a) :
    ((μ.restrict (leafUnion C)) (treeCell P)).toReal =
      ∑ q ∈ prefixFiber C a P, (μ (treeCell q)).toReal := by
  rw [restriction_prefix_mass μ ha hC hP, ENNReal.toReal_sum]
  intro q _
  exact measure_ne_top _ _

theorem restriction_prefix_mass_bounds (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    {N a : ℕ} (ha : a ≤ N) {C : Finset (CellPath d)} (hC : C ⊆ dyadicPaths N)
    {P : (CellPath d)} (hP : P.length = a) {s : ℝ}
    (hm : ∀ q ∈ C, s ≤ (μ (treeCell q)).toReal ∧
      (μ (treeCell q)).toReal ≤ 2*s) :
    (prefixFiber C a P).card * s ≤
      ((μ.restrict (leafUnion C)) (treeCell P)).toReal ∧
    ((μ.restrict (leafUnion C)) (treeCell P)).toReal ≤
      (prefixFiber C a P).card * (2*s) := by
  rw [restriction_prefix_mass_real μ ha hC hP]
  constructor
  · calc
      _ = ∑ _q ∈ prefixFiber C a P, s := by simp
      _ ≤ _ := Finset.sum_le_sum fun q hq => (hm q (Finset.mem_filter.mp hq).1).1
  · calc
      _ ≤ ∑ _q ∈ prefixFiber C a P, 2*s :=
        Finset.sum_le_sum fun q hq => (hm q (Finset.mem_filter.mp hq).1).2
      _ = _ := by simp

theorem restriction_total_mass_real (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    {N : ℕ} {C : Finset (CellPath d)} (hC : C ⊆ dyadicPaths N) :
    (μ (leafUnion C)).toReal = ∑ q ∈ C, (μ (treeCell q)).toReal := by
  rw [measure_leafUnion μ hC, ENNReal.toReal_sum]
  intro q _; exact measure_ne_top _ _

theorem restriction_total_mass_bounds (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    {N : ℕ} {C : Finset (CellPath d)} (hC : C ⊆ dyadicPaths N) {s : ℝ}
    (hm : ∀ q ∈ C, s ≤ (μ (treeCell q)).toReal ∧
      (μ (treeCell q)).toReal ≤ 2*s) :
    C.card*s ≤ (μ (leafUnion C)).toReal ∧
      (μ (leafUnion C)).toReal ≤ C.card*(2*s) := by
  rw [restriction_total_mass_real μ hC]
  constructor
  · calc
      _ = ∑ _q ∈ C, s := by simp
      _ ≤ _ := Finset.sum_le_sum fun q hq => (hm q hq).1
  · calc
      _ ≤ ∑ _q ∈ C, 2*s := Finset.sum_le_sum fun q hq => (hm q hq).2
      _ = _ := by simp

theorem leafUnion_all (N : ℕ) : leafUnion (dyadicPaths (d := d) N) = treeCell [] := treeCell_cover_root N

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
