import OAI.Analysis.CircleDomains.Probability.MeasurableBaireBranch

namespace OAI

/-! A continuous surjection from Baire space has a right inverse
measurable for any fixed completed finite Borel measure. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem exists_nullMeasurable_baire_rightInverse {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (g : (ℕ → ℕ) → X) (hg : Continuous g) (hsurj : Surjective g) :
    ∃ b : X → (ℕ → ℕ), NullMeasurable b μ ∧ ∀ x, g (b x) = x := by
  let A : List ℕ → Set X := fun s => g '' baireWordCylinder s
  have hA (s : List ℕ) : NullMeasurableSet (A s) μ :=
    nullMeasurableSet_analytic_finite μ ((isOpen_baireWordCylinder s).analyticSet_image hg)
  have hroot : A [] = univ := by
    simp only [A,baireWordCylinder_nil,image_univ,hsurj.range_eq]
  have hchild (s : List ℕ) : A s ⊆ ⋃ k, A (k::s) := by
    dsimp only [A]
    rw [← image_iUnion,baireWordCylinder_children]
  obtain ⟨b,hb,hbranch⟩ := exists_nullMeasurable_baire_branch μ A hA hroot hchild
  refine ⟨b,hb,?_⟩
  intro x
  symm
  apply eq_of_prefix_closures hg
  intro n
  have hx := hbranch x n
  have he : baireWordCylinder (PiNat.res (b x) n) = PiNat.cylinder (b x) n := by
    rw [PiNat.cylinder_eq_res]
    ext c
    simp only [baireWordCylinder,PiNat.res_length,mem_ofPred_eq]
  change x ∈ g '' baireWordCylinder (PiNat.res (b x) n) at hx
  exact subset_closure (he ▸ hx)

end CircleDomainRigidity

end

end OAI
