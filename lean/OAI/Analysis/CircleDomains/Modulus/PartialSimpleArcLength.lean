import OAI.Analysis.CircleDomains.Modulus.DisjointArcLengths
import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationPushforward

namespace OAI

/-! Finite physical length of a simple quotient arc follows from the
Hausdorff length of its physical part. No boundary extension of its
physical lift is required. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

theorem partial_simple_arc_dyadic_sum_le
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {V : Set PathTime} (f : PathTime → Y) (hf : ContinuousOn f V) (hinj : InjOn f V)
    (n : ℕ) :
    (∑ i : Fin (2 ^ n), if Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V then
      eVariationOn f (Icc (dyadicLeft n i) (dyadicRight n i)) else 0) ≤
      (μH[1] : Measure Y) (f '' V) := by
  let J := {i : Fin (2 ^ n) | Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V}
  have hdis : Pairwise (fun i j : J => Disjoint
      (Ioc (dyadicLeft n i.val) (dyadicRight n i.val))
      (Ioc (dyadicLeft n j.val) (dyadicRight n j.val))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro t ht hs
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have hsep : dyadicRight n i.val ≤ dyadicLeft n j.val :=
        dyadicReal_mono n (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (ht.2.trans hsep)) hs.1
    · have hsep : dyadicRight n j.val ≤ dyadicLeft n i.val :=
        dyadicReal_mono n (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (hs.2.trans hsep)) ht.1
  have h := sum_disjoint_arc_variations_le f hf hinj
    (fun i : J => dyadicLeft n i.val) (fun i : J => dyadicRight n i.val)
    (fun i => dyadicLeft_le_right n i.val) (fun i => i.property) hdis
  have he : (∑ i : J, eVariationOn f (Icc (dyadicLeft n i.val) (dyadicRight n i.val))) =
      ∑ i : Fin (2 ^ n), if Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V then
        eVariationOn f (Icc (dyadicLeft n i) (dyadicRight n i)) else 0 := by
    simpa only [tsum_fintype, J, Set.indicator_apply, Set.mem_ofPred_eq] using
      tsum_subtype J (fun i => eVariationOn f (Icc (dyadicLeft n i) (dyadicRight n i)))
  rwa [he] at h

theorem physicalValue_path_continuousOn
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) :
    ContinuousOn (physicalValue e y₀ ∘ γ) (γ ⁻¹' U) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h : Continuous (fun t : γ ⁻¹' U => (e.symm ⟨γ t.val, t.property⟩).val) :=
    continuous_subtype_val.comp (e.symm.continuous.comp
      ((γ.continuous.comp continuous_subtype_val).subtype_mk _))
  apply h.congr
  intro t
  change (e.symm ⟨γ t.val, t.property⟩).val = physicalValue e y₀ (γ t.val)
  rw [physicalValue, dite_eq_left (show γ t.val ∈ U from t.property)]

theorem physicalValue_path_injOn
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) (hγ : Injective γ) :
    InjOn (physicalValue e y₀ ∘ γ) (γ ⁻¹' U) := by
  intro s hs t ht heq
  change γ s ∈ U at hs
  change γ t ∈ U at ht
  apply hγ
  simp only [Function.comp_apply, physicalValue, dite_eq_left hs, dite_eq_left ht] at heq
  have hsub : e.symm ⟨γ s, hs⟩ = e.symm ⟨γ t, ht⟩ := Subtype.ext heq
  exact congrArg Subtype.val (e.symm.injective hsub)

theorem physicalSubpath_variation_eq_value
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) {a b : PathTime}
    (hab : a ≤ b) (hγ : γ ∈ pathsInsideOn U a b) :
    eVariationOn (physicalSubpath e hab ⟨γ, hγ⟩) univ =
      eVariationOn (physicalValue e y₀ ∘ γ) (Icc a b) := by
  have he : (physicalSubpath e hab ⟨γ, hγ⟩ : PathTime → Y) =
      (physicalValue e y₀ ∘ γ) ∘ timeClip a b := by
    funext t
    have ht : timeClip a b t ∈ Icc a b := by
      rw [← range_timeClip hab]
      exact mem_range_self t
    simp only [Function.comp_apply, physicalSubpath, ContinuousMap.coe_mk,
      physicalValue, dite_eq_left (hγ ht)]
  rw [he, eVariationOn.comp_eq_of_monotoneOn _ _
    ((monotone_timeClip a b).monotoneOn univ), image_univ, range_timeClip hab]

theorem simple_quotient_arc_physical_length_le
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) (hγ : Injective γ) :
    physicalDomainLength e y₀ γ ≤
      (μH[1] : Measure Y) ((physicalValue e y₀ ∘ γ) '' (γ ⁻¹' U)) := by
  apply iSup_le
  intro n
  have he : physicalStageLength e y₀ n γ =
      ∑ i : Fin (2 ^ n), if Icc (dyadicLeft n i) (dyadicRight n i) ⊆ γ ⁻¹' U then
        eVariationOn (physicalValue e y₀ ∘ γ) (Icc (dyadicLeft n i) (dyadicRight n i)) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
    · have hi' : Icc (dyadicLeft n i) (dyadicRight n i) ⊆ γ ⁻¹' U := hi
      rw [physicalDyadicLength, physicalDyadicPath_of_mem e y₀ n i γ hi,
        physicalSubpath_variation_eq_value e y₀ γ _ hi, ite_eq_left hi']
    · have hi' : ¬ Icc (dyadicLeft n i) (dyadicRight n i) ⊆ γ ⁻¹' U := hi
      simp only [physicalDyadicLength, physicalDyadicPath, totalPhysicalSubpath,
        dite_eq_right hi, ite_eq_right hi']
      exact (eVariationOn.eq_zero_iff _).mpr (fun _ _ _ _ => edist_self _)
  rw [he]
  exact partial_simple_arc_dyadic_sum_le _ (physicalValue_path_continuousOn e y₀ γ)
    (physicalValue_path_injOn e y₀ γ hγ) n

theorem simple_quotient_arc_physical_length_le_preimage
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (π : Y → X)
    (hπ : ∀y : G, π y.val = (e y).val)
    (γ : C(PathTime, X)) (hγ : Injective γ) {H : Set X} (hγH : range γ ⊆ H) :
    physicalDomainLength e y₀ γ ≤ (μH[1] : Measure Y) (π ⁻¹' H ∩ G) := by
  apply (simple_quotient_arc_physical_length_le e y₀ γ hγ).trans
  apply measure_mono
  rintro y ⟨t, ht, rfl⟩
  change γ t ∈ U at ht
  change π (physicalValue e y₀ (γ t)) ∈ H ∧ physicalValue e y₀ (γ t) ∈ G
  simp only [physicalValue, dite_eq_left ht]
  refine ⟨?_, (e.symm ⟨γ t, ht⟩).property⟩
  rw [hπ]
  simpa only [Homeomorph.apply_symm_apply] using hγH (mem_range_self t)

end CircleDomainRigidity

end

end OAI
