import OAI.MeasureTheory.Falconer.Incidence.BlockRegularization

namespace OAI

/-!
# Selecting the regular classes with their original masses

Classes are disjoint unions of original leaves. Discarding small leaves
costs 2^(-2N), and discarding small classes costs their number times the
class threshold. No lower density of the original law is required.
-/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def regularizationIndex (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (t : ℝ≥0∞) : Finset (List ℕ) :=
  ((regularizationLeaves Q μ N).image (regularizationLabel Q μ N B)).filter
    (fun T => t ≤ classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T univ)

noncomputable def regularizationSet (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (T : List ℕ) : Set (Space d) :=
  leafUnion Q (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T)

theorem regularizationSet_measurable (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (T : List ℕ) : MeasurableSet (regularizationSet Q μ N B T) :=
  leafUnion_measurable Q _

theorem regularizationIndex_card (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (t : ℝ≥0∞) :
    (regularizationIndex Q μ N B t).card ≤ (d*N+1)^(N/B+1)*((d+2)*N+1) :=
  (Finset.card_filter_le _ _).trans (regularization_label_count Q μ N B)

theorem regularizationSet_disjoint (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N B : ℕ) {T U : List ℕ} (h : T ≠ U) :
    Disjoint (regularizationSet Q μ N B T) (regularizationSet Q μ N B U) :=
  leafUnion_disjoint Q hQ
    (fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
    (fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
    (classLeaves_disjoint _ _ h)

theorem regularizationSet_mass (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (t : ℝ≥0∞) {T : List ℕ} (hT : T ∈ regularizationIndex Q μ N B t) :
    t ≤ μ (regularizationSet Q μ N B T) := by
  simpa only [regularizationSet,classMeasure,Measure.restrict_apply_univ] using (Finset.mem_filter.mp hT).2

theorem regularization_small_leaves_mass (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N : ℕ) :
    μ (leafUnion Q (cubePaths d N \ regularizationLeaves Q μ N)) ≤ ((2 : ℝ≥0∞)^(2*N))⁻¹ := by
  apply (discarded_leaves_mass Q hQ μ N ((2 : ℝ≥0∞)^((d+2)*N))⁻¹).trans_eq
  rw [Nat.add_mul,pow_add,ENNReal.mul_inv (by simp) (by simp),← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp),one_mul]

theorem regularization_discarded_mass (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N B : ℕ) (t : ℝ≥0∞) :
    μ (Q.carrier \ ⋃ T ∈ regularizationIndex Q μ N B t, regularizationSet Q μ N B T) ≤
      ((2 : ℝ≥0∞)^(2*N))⁻¹ + ((d*N+1)^(N/B+1)*((d+2)*N+1) : ℕ)*t := by
  let L := regularizationLeaves Q μ N
  let f := regularizationLabel Q μ N B
  let bad := (L.image f).filter (fun T => classMeasure Q μ L f T univ < t)
  have hsub : (Q.carrier \ ⋃ T ∈ regularizationIndex Q μ N B t, regularizationSet Q μ N B T) ⊆
      leafUnion Q (cubePaths d N \ L) ∪ ⋃ T ∈ bad, leafUnion Q (classLeaves L f T) := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth N hx.1
    by_cases hpL : p ∈ L
    · have hf : f p ∈ L.image f := Finset.mem_image.mpr ⟨p,hpL,rfl⟩
      by_cases hb : classMeasure Q μ L f (f p) univ < t
      · exact Or.inr (mem_iUnion₂.mpr ⟨f p,Finset.mem_filter.mpr ⟨hf,hb⟩,
          mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hpL,rfl⟩,hxp⟩⟩)
      · have hi : f p ∈ regularizationIndex Q μ N B t :=
          Finset.mem_filter.mpr ⟨hf,le_of_not_gt hb⟩
        exact (hx.2 (mem_iUnion₂.mpr ⟨f p,hi,
          mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hpL,rfl⟩,hxp⟩⟩)).elim
    · exact Or.inl (mem_iUnion₂.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hp,hpL⟩,hxp⟩)
  apply (measure_mono hsub).trans (measure_union_le _ _ |>.trans ?_)
  apply add_le_add (regularization_small_leaves_mass Q hQ μ N)
  dsimp only [bad]
  apply (discarded_classes_mass Q μ L f t).trans
  exact mul_le_mul' (by exact_mod_cast regularization_label_count Q μ N B) le_rfl

end Falconer.Regularization

end OAI
