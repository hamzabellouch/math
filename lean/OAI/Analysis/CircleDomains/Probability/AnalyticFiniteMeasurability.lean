import OAI.Analysis.CircleDomains.Selection.AnalyticWordBranch

namespace OAI

/-! Finite Borel measures see continuous Baire images in their completion.
Measurable hulls of finite-prefix images have null child defects; outside
all defects, an infinite branch recovers a point of the actual image. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem nullMeasurableSet_baire_image_finite {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) : NullMeasurableSet (range f) μ := by
  classical
  let A : List ℕ → Set X := fun s => f '' baireWordCylinder s
  let B : List ℕ → Set X := fun s => toMeasurable μ (A s) ∩ closure (A s)
  have hB (s : List ℕ) : MeasurableSet (B s) :=
    (measurableSet_toMeasurable μ (A s)).inter isClosed_closure.measurableSet
  have hAB (s : List ℕ) : A s ⊆ B s :=
    fun _ hx => ⟨subset_toMeasurable μ _ hx,subset_closure hx⟩
  have hmeasure (s : List ℕ) : μ (B s) = μ (A s) :=
    le_antisymm ((measure_mono inter_subset_left).trans_eq (measure_toMeasurable (A s)))
      (measure_mono (hAB s))
  have hchildren (s : List ℕ) : (⋃ k, A (k::s)) = A s := by
    dsimp only [A]
    rw [← image_iUnion,baireWordCylinder_children]
  let N : List ℕ → Set X := fun s => B s \ ⋃ k, B (k::s)
  have hN (s : List ℕ) : μ (N s) = 0 := by
    have hc : A s ⊆ B s ∩ ⋃ k, B (k::s) := by
      intro x hx
      refine ⟨hAB s hx,?_⟩
      obtain ⟨k,hk⟩ := mem_iUnion.mp ((hchildren s).symm ▸ hx)
      exact mem_iUnion.mpr ⟨k,hAB (k::s) hk⟩
    have he : μ (B s ∩ ⋃ k, B (k::s)) = μ (B s) :=
      le_antisymm (measure_mono inter_subset_left)
        ((hmeasure s).le.trans (measure_mono hc))
    have hh := measure_sdiff inter_subset_left
      ((hB s).inter (MeasurableSet.iUnion (fun k => hB (k::s)))).nullMeasurableSet
      (measure_ne_top μ (B s ∩ ⋃ k, B (k::s)))
    rw [he,tsub_self] at hh
    simpa only [N,sdiff_inter,sdiff_self,empty_union] using hh
  have hnull : μ (⋃ s, N s) = 0 := measure_iUnion_null hN
  have heq : B [] =ᵐ[μ] range f := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    apply propext
    constructor
    · intro hroot
      apply mem_range_of_word_hull_branch hf B hroot
      · intro s hs
        by_contra hn
        apply hx
        exact mem_iUnion.mpr ⟨s,hs,by simpa only [mem_iUnion,not_exists] using hn⟩
      · exact fun s => inter_subset_right
    · intro hx
      apply hAB []
      simpa only [A,baireWordCylinder_nil,image_univ] using hx
  exact (hB []).nullMeasurableSet.congr heq

 theorem nullMeasurableSet_analytic_finite {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {A : Set X} (hA : AnalyticSet A) : NullMeasurableSet A μ := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f,hf,rfl⟩
  · exact nullMeasurableSet_empty
  · exact nullMeasurableSet_baire_image_finite μ f hf

 theorem finiteTorusAnalyticMeasurability : FiniteTorusAnalyticMeasurability := by
  intro d E hE
  rw [AnalyticSet] at hE
  rcases hE with rfl | ⟨f,hf,rfl⟩
  · exact nullMeasurableSet_empty
  · exact nullMeasurableSet_baire_image_finite _ f hf

end CircleDomainRigidity

end

end OAI
