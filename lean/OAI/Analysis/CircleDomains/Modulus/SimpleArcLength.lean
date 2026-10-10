import OAI.Analysis.CircleDomains.Modulus.HausdorffPayment
import OAI.Analysis.CircleDomains.Probability.PathLengthMeasure

namespace OAI

/-! The variation of an injective arc is paid by the Hausdorff length of
its image. Disjoint parameter intervals have disjoint half-open images. -/

open Set Function MeasureTheory Metric
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_edist_le_length_Ioc
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : PathTime → X) {s : Set PathTime} (hs : OrdConnected s)
    (hf : ContinuousOn f s) {a b : PathTime} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≤ b) : edist (f b) (f a) ≤ (μH[1] : Measure X) (f '' Ioc a b) := by
  let : NullSingletonClass (μH[1] : Measure X) :=
    Measure.nullSingletonClass_hausdorff X (by norm_num)
  have hsub : Icc a b ⊆ s := hs.out ha hb
  have hc : IsPreconnected (f '' Icc a b) :=
    isPreconnected_Icc.image f (hf.mono hsub)
  have hd := dist_le_hausdorffMeasure_one_of_preconnected hc
    (mem_image_of_mem f (left_mem_Icc.mpr hab))
    (mem_image_of_mem f (right_mem_Icc.mpr hab))
  rw [edist_dist]
  apply hd.trans
  have hi : f '' Icc a b ⊆ insert (f a) (f '' Ioc a b) := by
    rintro _ ⟨t, ht, rfl⟩
    rcases ht.1.eq_or_lt with h | h
    · exact Or.inl (congrArg f h.symm)
    · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
  calc
    _ ≤ (μH[1] : Measure X) (insert (f a) (f '' Ioc a b)) := measure_mono hi
    _ ≤ (μH[1] : Measure X) {f a} + (μH[1] : Measure X) (f '' Ioc a b) :=
      measure_union_le _ _
    _ = _ := by rw [measure_singleton, zero_add]

theorem simple_arc_variation_le_length
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : PathTime → X) {s : Set PathTime} (hs : OrdConnected s)
    (hf : ContinuousOn f s) (hinj : InjOn f s) :
    eVariationOn f s ≤ (μH[1] : Measure X) (f '' s) := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  let A : ℕ → Set X := fun i => f '' Ioc (u i) (u (i + 1))
  have hA (i : ℕ) : MeasurableSet (A i) := by
    have hsub : Icc (u i) (u (i + 1)) ⊆ s := hs.out (hus i) (hus (i + 1))
    have hcompact : IsCompact (f '' Icc (u i) (u (i + 1))) :=
      isCompact_Icc.image_of_continuousOn (hf.mono hsub)
    have he : A i = f '' Icc (u i) (u (i + 1)) \ {f (u i)} := by
      ext x
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨⟨t, Ioc_subset_Icc_self ht, rfl⟩, ?_⟩
        intro heq
        exact ht.1.ne' (hinj (hsub (Ioc_subset_Icc_self ht)) (hus i) heq)
      · rintro ⟨⟨t, ht, rfl⟩, hne⟩
        refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, ht.2⟩, rfl⟩
        intro heq
        exact hne (congrArg f heq.symm)
    rw [he]
    exact hcompact.isClosed.measurableSet.diff (measurableSet_singleton _)
  have hdis : Pairwise (Disjoint on A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ ⟨v, hv, heq⟩
    have hts : t ∈ s := hs.out (hus i) (hus (i + 1)) (Ioc_subset_Icc_self ht)
    have hvs : v ∈ s := hs.out (hus j) (hus (j + 1)) (Ioc_subset_Icc_self hv)
    have htv : t = v := hinj hts hvs heq.symm
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact (not_lt_of_ge (ht.2.trans (hu (Nat.succ_le_of_lt hij)))) (htv ▸ hv.1)
    · exact (not_lt_of_ge (hv.2.trans (hu (Nat.succ_le_of_lt hji)))) (htv.symm ▸ ht.1)
  calc
    _ ≤ ∑ i ∈ Finset.range n, (μH[1] : Measure X) (A i) := by
      apply Finset.sum_le_sum
      intro i _
      exact simple_arc_edist_le_length_Ioc f hs hf (hus i) (hus (i + 1))
        (hu (Nat.le_succ i))
    _ = (μH[1] : Measure X) (⋃ i ∈ Finset.range n, A i) := by
      rw [measure_biUnion_finset (fun i _ j _ hij => hdis hij) (fun i _ => hA i)]
    _ ≤ (μH[1] : Measure X) (f '' s) := by
      apply measure_mono
      intro x hx
      obtain ⟨i, _, t, ht, rfl⟩ := mem_iUnion₂.mp hx
      exact ⟨t, hs.out (hus i) (hus (i + 1)) (Ioc_subset_Icc_self ht), rfl⟩

end CircleDomainRigidity

end

end OAI
