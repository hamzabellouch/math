import OAI.Analysis.CircleDomains.Modulus.DisjointArcLengths

namespace OAI

/-! Disjoint portions of a simple arc have disjoint image measures after
their shared endpoints, which have zero Hausdorff length, are removed. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem arc_image_Icc_ae_eq_Ioc {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NullSingletonClass μ] (f : PathTime → X) (a b : PathTime) :
    f '' Icc a b =ᵐ[μ] f '' Ioc a b := by
  filter_upwards [μ.ae_ne (f a)] with x hx
  apply propext
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, ht.2⟩, rfl⟩
    intro heq
    exact hx (congrArg f heq.symm)
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Ioc_subset_Icc_self ht, rfl⟩

theorem sum_disjoint_arc_image_measures_le {ι X : Type*} [Fintype ι]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [NullSingletonClass μ]
    {V : Set PathTime} (f : PathTime → X) (hf : ContinuousOn f V) (hinj : InjOn f V)
    (a b : ι → PathTime) (hab : ∀ i, a i ≤ b i)
    (hsub : ∀ i, Icc (a i) (b i) ⊆ V)
    (hdis : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    (∑ i, μ.restrict (f '' Icc (a i) (b i))) ≤ μ.restrict (f '' V) := by
  have himdis : Pairwise (fun i j => Disjoint
      (f '' Ioc (a i) (b i)) (f '' Ioc (a j) (b j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ ⟨s, hs, heq⟩
    have hts := hinj (hsub i (Ioc_subset_Icc_self ht)) (hsub j (Ioc_subset_Icc_self hs)) heq.symm
    exact Set.disjoint_left.mp (hdis hij) ht (hts.symm ▸ hs)
  calc
    _ = ∑ i, μ.restrict (f '' Ioc (a i) (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Measure.restrict_congr_set (arc_image_Icc_ae_eq_Ioc μ f (a i) (b i))
    _ = μ.restrict (⋃ i, f '' Ioc (a i) (b i)) := by
      rw [Measure.restrict_iUnion himdis
        (fun i => simple_arc_Ioc_image_measurable f hf hinj (hab i) (hsub i)),
        Measure.sum_fintype]
    _ ≤ _ := Measure.restrict_mono
      (iUnion_subset fun i => image_mono (Ioc_subset_Icc_self.trans (hsub i))) le_rfl

end CircleDomainRigidity

end

end OAI
