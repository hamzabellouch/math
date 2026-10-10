import OAI.Analysis.CircleDomains.Probability.SimpleArcOccupation

namespace OAI

/-! Disjoint compact portions of a simple arc have a total length bounded
by the Hausdorff length of the whole arc, even when the map is only
continuous on an open part of its parameter domain. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_Ioc_image_measurable
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {V : Set PathTime} (f : PathTime → X) (hf : ContinuousOn f V) (hinj : InjOn f V)
    {a b : PathTime} (hab : a ≤ b) (hsub : Icc a b ⊆ V) :
    MeasurableSet (f '' Ioc a b) := by
  have hcompact : IsCompact (f '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn (hf.mono hsub)
  have he : f '' Ioc a b = f '' Icc a b \ {f a} := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, Ioc_subset_Icc_self ht, rfl⟩, ?_⟩
      intro heq
      exact ht.1.ne' (hinj (hsub (Ioc_subset_Icc_self ht))
        (hsub (left_mem_Icc.mpr hab)) heq)
    · rintro ⟨⟨t, ht, rfl⟩, hne⟩
      refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, ht.2⟩, rfl⟩
      intro heq
      exact hne (congrArg f heq.symm)
  rw [he]
  exact hcompact.isClosed.measurableSet.diff (measurableSet_singleton _)

theorem simple_arc_variation_le_Ioc_image
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {V : Set PathTime} (f : PathTime → X) (hf : ContinuousOn f V) (hinj : InjOn f V)
    {a b : PathTime} (_hab : a ≤ b) (hsub : Icc a b ⊆ V) :
    eVariationOn f (Icc a b) ≤ (μH[1] : Measure X) (f '' Ioc a b) := by
  let : NullSingletonClass (μH[1] : Measure X) :=
    Measure.nullSingletonClass_hausdorff X (by norm_num)
  have hi : f '' Icc a b ⊆ {f a} ∪ (f '' Ioc a b) := by
    rintro _ ⟨t, ht, rfl⟩
    rcases ht.1.eq_or_lt with h | h
    · exact Or.inl (congrArg f h.symm)
    · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
  calc
    _ ≤ (μH[1] : Measure X) (f '' Icc a b) :=
      simple_arc_variation_le_length f ordConnected_Icc (hf.mono hsub) (hinj.mono hsub)
    _ ≤ (μH[1] : Measure X) ({f a} ∪ (f '' Ioc a b)) := measure_mono hi
    _ ≤ (μH[1] : Measure X) {f a} + (μH[1] : Measure X) (f '' Ioc a b) := measure_union_le _ _
    _ = _ := by rw [measure_singleton, zero_add]

theorem sum_disjoint_arc_variations_le {ι X : Type*} [Fintype ι]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {V : Set PathTime} (f : PathTime → X) (hf : ContinuousOn f V) (hinj : InjOn f V)
    (a b : ι → PathTime) (hab : ∀ i, a i ≤ b i)
    (hsub : ∀ i, Icc (a i) (b i) ⊆ V)
    (hdis : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    (∑ i, eVariationOn f (Icc (a i) (b i))) ≤ (μH[1] : Measure X) (f '' V) := by
  have himdis : Pairwise (fun i j => Disjoint
      (f '' Ioc (a i) (b i)) (f '' Ioc (a j) (b j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ ⟨s, hs, heq⟩
    have hts := hinj (hsub i (Ioc_subset_Icc_self ht)) (hsub j (Ioc_subset_Icc_self hs)) heq.symm
    exact Set.disjoint_left.mp (hdis hij) ht (hts.symm ▸ hs)
  calc
    _ ≤ ∑ i, (μH[1] : Measure X) (f '' Ioc (a i) (b i)) :=
      Finset.sum_le_sum (fun i _ => simple_arc_variation_le_Ioc_image f hf hinj (hab i) (hsub i))
    _ = (μH[1] : Measure X) (⋃ i, f '' Ioc (a i) (b i)) := by
      rw [measure_iUnion himdis (fun i => simple_arc_Ioc_image_measurable f hf hinj (hab i) (hsub i)),
        tsum_fintype]
    _ ≤ _ := measure_mono (iUnion_subset fun i => image_mono (Ioc_subset_Icc_self.trans (hsub i)))

end CircleDomainRigidity

end

end OAI
