import Mathlib

namespace OAI

noncomputable section

open Set SetRel UniformSpace
open scoped Uniformity ENNReal

namespace Problem340

theorem dynCover_prefix_product
    {X : Type*} [Nonempty X] (T : X → X) (F : Set X)
    (U : SetRel X X) [U.IsSymm] (n : ℕ) (s t : Finset X)
    (hs : Dynamics.IsDynCoverOf T F U 1 s)
    (ht : Dynamics.IsDynCoverOf T (T '' F) U n t) :
    ∃ c : Finset X,
      Dynamics.IsDynCoverOf T F (U ○ U) (n + 1) c ∧
      c.card ≤ s.card * t.card := by
  classical
  have hchoose : ∀ p : s × t, ∃ y : X, ∀ x ∈ F,
      (x, (p.1 : X)) ∈ U → (T x, (p.2 : X)) ∈ Dynamics.dynEntourage T U n →
      (x, y) ∈ Dynamics.dynEntourage T (U ○ U) (n + 1) := by
    intro p
    by_cases h : ∃ z ∈ F, (z, (p.1 : X)) ∈ U ∧
        (T z, (p.2 : X)) ∈ Dynamics.dynEntourage T U n
    · obtain ⟨z, hzF, hzU, hzD⟩ := h
      refine ⟨z, ?_⟩
      intro x hxF hxU hxD
      rw [Dynamics.mem_dynEntourage]
      intro k hk
      cases k with
      | zero =>
          simpa only [Function.iterate_zero, id_eq] using
            (show (x, z) ∈ U ○ U from ⟨p.1, hxU, U.symm hzU⟩)
      | succ k =>
          have hk' : k < n := Nat.lt_of_succ_lt_succ hk
          have hxk := Dynamics.mem_dynEntourage.mp hxD k hk'
          have hzk := Dynamics.mem_dynEntourage.mp hzD k hk'
          simpa only [Function.iterate_succ_apply] using
            (show (T^[k] (T x), T^[k] (T z)) ∈ U ○ U from
              ⟨T^[k] (p.2 : X), hxk, U.symm hzk⟩)
    · refine ⟨Classical.choice inferInstance, ?_⟩
      intro x hxF hxU hxD
      exact (h ⟨x, hxF, hxU, hxD⟩).elim
  choose pick hpick using hchoose
  refine ⟨Finset.univ.image pick, ?_, ?_⟩
  · intro x hxF
    obtain ⟨a, ha, hxa⟩ := hs hxF
    obtain ⟨b, hb, hxb⟩ := ht (mem_image_of_mem T hxF)
    let p : s × t := (⟨a, ha⟩, ⟨b, hb⟩)
    refine ⟨pick p, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩, ?_⟩
    apply hpick p x hxF
    · simpa only [Dynamics.dynEntourage_one] using hxa
    · exact hxb
  · exact (Finset.card_image_le).trans (by simp)

theorem coverMincard_le_initial_card_mul_image
    {X : Type*} [Nonempty X] (T : X → X) (F : Set X)
    (U : SetRel X X) [U.IsSymm] (s : Finset X)
    (hs : Dynamics.IsDynCoverOf T F U 1 s) (n : ℕ) :
    Dynamics.coverMincard T F (U ○ U) n ≤
      (s.card : ℕ∞) * Dynamics.coverMincard T (T '' F) U n := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp [Dynamics.coverMincard_empty]
  rcases eq_top_or_lt_top (Dynamics.coverMincard T (T '' F) U n) with htop | hfin
  · have hcard : (s.card : ℕ∞) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr (hs.nonempty hF)).ne'
    simp [htop, hcard]
  · obtain ⟨t, ht, hcard⟩ :=
      (Dynamics.coverMincard_finite_iff T (T '' F) U n).mp hfin
    obtain ⟨c, hc, hct⟩ := dynCover_prefix_product T F U n s t hs ht
    calc
      Dynamics.coverMincard T F (U ○ U) n ≤ (c.card : ℕ∞) :=
        (hc.of_le (Nat.le_succ n)).coverMincard_le_card
      _ ≤ (s.card * t.card : ℕ) := by exact_mod_cast hct
      _ = (s.card : ℕ∞) * Dynamics.coverMincard T (T '' F) U n := by
        rw [Nat.cast_mul, hcard]

theorem coverEntropyEntourage_le_image_of_initial_cover
    {X : Type*} [Nonempty X] (T : X → X) (F : Set X)
    (U : SetRel X X) [U.IsSymm] (s : Finset X)
    (hs : Dynamics.IsDynCoverOf T F U 1 s) :
    Dynamics.coverEntropyEntourage T F (U ○ U) ≤
      Dynamics.coverEntropyEntourage T (T '' F) U := by
  apply ExpGrowth.expGrowthSup_le_of_eventually_le (b := (s.card : ℝ≥0∞)) (by simp)
  apply Filter.Eventually.of_forall
  intro n
  simpa only [ENat.toENNReal_mul, ENat.toENNReal_coe] using
    ENat.toENNReal_mono (coverMincard_le_initial_card_mul_image T F U s hs n)

theorem coverEntropy_le_image_of_isCompact
    {X : Type*} [UniformSpace X] [Nonempty X]
    (T : X → X) (F : Set X) (hF : IsCompact F) :
    Dynamics.coverEntropy T F ≤ Dynamics.coverEntropy T (T '' F) := by
  apply iSup₂_le
  intro U hU
  obtain ⟨V, hV, hVsymm, hVU⟩ := comp_symm_mem_uniformity_sets hU
  obtain ⟨s, hs⟩ := Dynamics.exists_isDynCoverOf_of_isCompact_uniformContinuous
    hF uniformContinuous_id hV 1
  have hsT : Dynamics.IsDynCoverOf T F V 1 s := by
    simpa only [Dynamics.IsDynCoverOf, Dynamics.dynEntourage_one] using hs
  exact ((Dynamics.coverEntropyEntourage_antitone T F hVU).trans
    (coverEntropyEntourage_le_image_of_initial_cover T F V s hsT)).trans
    (Dynamics.coverEntropyEntourage_le_coverEntropy T (T '' F) hV)

theorem coverEntropy_univ_eq_range
    {X : Type*} [UniformSpace X] [CompactSpace X] [Nonempty X]
    (T : X → X) :
    Dynamics.coverEntropy T (Set.univ : Set X) =
      Dynamics.coverEntropy T (Set.range T) := by
  rw [← image_univ]
  exact le_antisymm (coverEntropy_le_image_of_isCompact T univ isCompact_univ)
    (Dynamics.coverEntropy_monotone T (Set.subset_univ _))

theorem coverEntropy_univ_eq_zero_of_image_subset
    {X : Type*} [UniformSpace X] [CompactSpace X] [Nonempty X]
    (T : X → X) (K : Set X) (hTK : Set.range T ⊆ K)
    (hK : Dynamics.coverEntropy T K = 0) :
    Dynamics.coverEntropy T (Set.univ : Set X) = 0 := by
  apply le_antisymm
  · have h := coverEntropy_le_image_of_isCompact T univ isCompact_univ
    rw [image_univ] at h
    exact h.trans ((Dynamics.coverEntropy_monotone T hTK).trans_eq hK)
  · exact Dynamics.coverEntropy_nonneg T Set.univ_nonempty

theorem coverEntropy_univ_eq_zero_of_first_image_factor
    {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    [CompactSpace X] [Nonempty X]
    (T : X → X) (S : Y → Y) (φ : Y → X)
    (hsemi : Function.Semiconj φ S T) (hφ : UniformContinuous φ)
    (himage : Set.range T ⊆ Set.range φ)
    (hS : Dynamics.coverEntropy S (Set.univ : Set Y) = 0) :
    Dynamics.coverEntropy T (Set.univ : Set X) = 0 := by
  apply le_antisymm
  · have h := coverEntropy_le_image_of_isCompact T univ isCompact_univ
    rw [image_univ] at h
    have hfac := Dynamics.coverEntropy_image_le_of_uniformContinuous hsemi hφ univ
    rw [image_univ, hS] at hfac
    exact h.trans ((Dynamics.coverEntropy_monotone T himage).trans hfac)
  · exact Dynamics.coverEntropy_nonneg T Set.univ_nonempty

end Problem340

end

end OAI
