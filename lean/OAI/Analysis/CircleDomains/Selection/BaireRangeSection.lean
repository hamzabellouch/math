import OAI.Analysis.CircleDomains.Selection.BaireRightInverse

namespace OAI

/-! A completed-measure section on the range of a continuous Baire map.
The values off the range play no role in the lifting application. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

theorem exists_nullMeasurable_baire_rangeSection {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (g : (ℕ → ℕ) → X) (hg : Continuous g) :
    ∃ b : X → (ℕ → ℕ), NullMeasurable b μ ∧ ∀ x ∈ range g, g (b x) = x := by
  let A : List ℕ → Set X := fun s => g '' baireWordCylinder s ∪ (range g)ᶜ
  have hr : NullMeasurableSet (range g) μ := nullMeasurableSet_baire_image_finite μ g hg
  have hA (s : List ℕ) : NullMeasurableSet (A s) μ :=
    (nullMeasurableSet_analytic_finite μ
      ((isOpen_baireWordCylinder s).analyticSet_image hg)).union hr.compl
  have hroot : A [] = univ := by
    simp only [A, baireWordCylinder_nil, image_univ, union_compl_self]
  have hchild (s : List ℕ) : A s ⊆ ⋃ k, A (k::s) := by
    rintro x (hx | hx)
    · have : x ∈ ⋃ k, g '' baireWordCylinder (k::s) := by
        rw [← image_iUnion, baireWordCylinder_children]
        exact hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp this
      exact mem_iUnion.mpr ⟨k, Or.inl hk⟩
    · exact mem_iUnion.mpr ⟨0, Or.inr hx⟩
  obtain ⟨b, hb, hbranch⟩ := exists_nullMeasurable_baire_branch μ A hA hroot hchild
  refine ⟨b, hb, ?_⟩
  intro x hx
  symm
  apply eq_of_prefix_closures hg
  intro n
  have hh := (hbranch x n).resolve_right (not_not.mpr hx)
  have he : baireWordCylinder (PiNat.res (b x) n) = PiNat.cylinder (b x) n := by
    rw [PiNat.cylinder_eq_res]
    ext c
    simp only [baireWordCylinder, PiNat.res_length, mem_ofPred_eq]
  exact subset_closure (he ▸ hh)

end CircleDomainRigidity

end

end OAI
