import OAI.NumberTheory.TwoPoint.Bounds.CenterBandExpansion

namespace OAI

/-! Exact reindexing of the center-band expansion into retained and
removed prime subsets. Every original term is represented once. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem centerBand_nonraw_expansion (D : Finset ℕ)
    (hD : ∀ p ∈ D, Nat.Prime p) (θ : ℂ) (n : ℕ) :
    (∏ p ∈ D, (natDivisibilityIndicator p n - θ / (p : ℂ))) -
        natDivisibilityIndicator (∏ p ∈ D, p) n =
      ∑ W ∈ D.powerset.filter Finset.Nonempty,
        ((-θ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
          natDivisibilityIndicator (∏ p ∈ D \ W, p) n := by
  let F : Finset ℕ → ℂ := fun W =>
    ((-θ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
      natDivisibilityIndicator (∏ p ∈ D \ W, p) n
  have hF : F ∅ = natDivisibilityIndicator (∏ p ∈ D, p) n := by simp [F]
  have hfilter : D.powerset.filter Finset.Nonempty = D.powerset.erase ∅ := by
    ext W
    simp only [mem_filter, mem_erase, nonempty_iff_ne_empty]
    exact and_comm
  rw [centerBand_expansion D hD θ n, hfilter]
  change (∑ W ∈ D.powerset, F W) - _ = ∑ W ∈ D.powerset.erase ∅, F W
  rw [← sum_erase_add D.powerset F (empty_mem_powerset D), hF]
  ring

lemma primeIndicator_union (U V : Finset ℕ) (hU : ∀ p ∈ U, Nat.Prime p)
    (hV : ∀ p ∈ V, Nat.Prime p) (hd : Disjoint U V) (n : ℕ) :
    natDivisibilityIndicator (∏ p ∈ U, p) n *
      natDivisibilityIndicator (∏ p ∈ V, p) n =
        natDivisibilityIndicator (∏ p ∈ U ∪ V, p) n := by
  rw [← natDivisibilityIndicator_product U hU n,
    ← natDivisibilityIndicator_product V hV n, ← prod_union hd]
  apply natDivisibilityIndicator_product
  intro p hp
  rcases mem_union.mp hp with hp | hp
  · exact hU p hp
  · exact hV p hp

/-- Only the selected center band is centered. The untouched core factors
combine with the retained center factors into the exact divisor `D\W`. -/
theorem partialCenterBand_expansion (D T : Finset ℕ)
    (hD : ∀ p ∈ D, Nat.Prime p) (θ : ℂ) (n : ℕ) :
    natDivisibilityIndicator (∏ p ∈ D \ T, p) n *
        (∏ p ∈ D ∩ T, (natDivisibilityIndicator p n - θ / (p : ℂ))) =
      ∑ W ∈ (D ∩ T).powerset,
        ((-θ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
          natDivisibilityIndicator (∏ p ∈ D \ W, p) n := by
  rw [centerBand_expansion (D ∩ T) (fun p hp => hD p (mem_inter.mp hp).1) θ n, mul_sum]
  apply sum_congr rfl
  intro W hW
  have hWT : W ⊆ T := (mem_powerset.mp hW).trans inter_subset_right
  have hd : Disjoint (D \ T) ((D ∩ T) \ W) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (mem_sdiff.mp hp).2 (mem_inter.mp (mem_sdiff.mp hq).1).2
  have heq : (D \ T) ∪ ((D ∩ T) \ W) = D \ W := by
    ext p
    simp only [mem_union, mem_sdiff, mem_inter]
    constructor
    · rintro (⟨hpD, hpT⟩ | ⟨⟨hpD, hpT⟩, hpW⟩)
      · exact ⟨hpD, fun hpW => hpT (hWT hpW)⟩
      · exact ⟨hpD, hpW⟩
    · rintro ⟨hpD, hpW⟩
      by_cases hpT : p ∈ T
      · exact Or.inr ⟨⟨hpD, hpT⟩, hpW⟩
      · exact Or.inl ⟨hpD, hpT⟩
  calc
    _ = ((-θ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
        (natDivisibilityIndicator (∏ p ∈ D \ T, p) n *
          natDivisibilityIndicator (∏ p ∈ (D ∩ T) \ W, p) n) := by ring
    _ = _ := by
      rw [primeIndicator_union (D \ T) ((D ∩ T) \ W)
        (fun p hp => hD p (mem_sdiff.mp hp).1)
        (fun p hp => hD p (mem_inter.mp (mem_sdiff.mp hp).1).1) hd n, heq]

theorem partialCenterBand_nonraw_expansion (D T : Finset ℕ)
    (hD : ∀ p ∈ D, Nat.Prime p) (θ : ℂ) (n : ℕ) :
    natDivisibilityIndicator (∏ p ∈ D \ T, p) n *
        (∏ p ∈ D ∩ T, (natDivisibilityIndicator p n - θ / (p : ℂ))) -
        natDivisibilityIndicator (∏ p ∈ D, p) n =
      ∑ W ∈ (D ∩ T).powerset.filter Finset.Nonempty,
        ((-θ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
          natDivisibilityIndicator (∏ p ∈ D \ W, p) n := by
  let F : Finset ℕ → ℂ := fun W =>
    ((-θ) ^ W.card / ((∏ p ∈ W, p : ℕ) : ℂ)) *
      natDivisibilityIndicator (∏ p ∈ D \ W, p) n
  have hF : F ∅ = natDivisibilityIndicator (∏ p ∈ D, p) n := by simp [F]
  have hfilter : (D ∩ T).powerset.filter Finset.Nonempty = (D ∩ T).powerset.erase ∅ := by
    ext W
    simp only [mem_filter, mem_erase, nonempty_iff_ne_empty]
    exact and_comm
  rw [partialCenterBand_expansion D T hD θ n, hfilter]
  change (∑ W ∈ (D ∩ T).powerset, F W) - _ = ∑ W ∈ (D ∩ T).powerset.erase ∅, F W
  rw [← sum_erase_add (D ∩ T).powerset F (empty_mem_powerset (D ∩ T)), hF]
  ring

lemma powerset_inter_filter (D T : Finset ℕ) :
    (D ∩ T).powerset = T.powerset.filter (fun W => W ⊆ D) := by
  ext W
  simp only [mem_powerset, mem_filter]
  constructor
  · intro h
    exact ⟨fun p hp => (mem_inter.mp (h hp)).2,
      fun p hp => (mem_inter.mp (h hp)).1⟩
  · rintro ⟨hT, hD⟩ p hp
    exact mem_inter.mpr ⟨hD hp, hT hp⟩

lemma sum_powerset_retained (S W : Finset ℕ) (hW : W ⊆ S)
    (F : Finset ℕ → ℂ) :
    (∑ D ∈ S.powerset.filter (fun D => W ⊆ D), F (D \ W)) =
      ∑ U ∈ (S \ W).powerset, F U := by
  apply sum_bij (fun D _ => D \ W)
  · intro D hD
    apply mem_powerset.mpr
    intro p hp
    exact mem_sdiff.mpr ⟨(mem_powerset.mp (mem_filter.mp hD).1) (mem_sdiff.mp hp).1,
      (mem_sdiff.mp hp).2⟩
  · intro D hD E hE heq
    calc
      D = (D \ W) ∪ W := (sdiff_union_of_subset (mem_filter.mp hD).2).symm
      _ = (E \ W) ∪ W := congrArg (fun V : Finset ℕ => V ∪ W) heq
      _ = E := sdiff_union_of_subset (mem_filter.mp hE).2
  · intro U hU
    have hUS : U ⊆ S := (mem_powerset.mp hU).trans sdiff_subset
    have hUW : ∀ p ∈ U, p ∉ W := fun p hp => (mem_sdiff.mp (mem_powerset.mp hU hp)).2
    refine ⟨U ∪ W, mem_filter.mpr ⟨mem_powerset.mpr (union_subset hUS hW), subset_union_right⟩, ?_⟩
    ext p
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hp | hp, hn⟩
      · exact hp
      · exact False.elim (hn hp)
    · intro hp
      exact ⟨Or.inl hp, hUW p hp⟩
  · intro D _
    rfl

/-- The removed-prime choice can be made first; the retained subset then
runs through the complementary pool. No cardinal multiplicity is added. -/
theorem centerBand_reindex (S T : Finset ℕ) (hT : T ⊆ S)
    (F : Finset ℕ → Finset ℕ → ℂ) :
    (∑ D ∈ S.powerset, ∑ W ∈ (D ∩ T).powerset, F (D \ W) W) =
      ∑ W ∈ T.powerset, ∑ U ∈ (S \ W).powerset, F U W := by
  calc
    _ = ∑ D ∈ S.powerset, ∑ W ∈ T.powerset,
        if W ⊆ D then F (D \ W) W else 0 := by
      apply sum_congr rfl
      intro D _
      rw [powerset_inter_filter, sum_filter]
    _ = ∑ W ∈ T.powerset, ∑ D ∈ S.powerset,
        if W ⊆ D then F (D \ W) W else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro W hW
      rw [← sum_filter]
      exact sum_powerset_retained S W ((mem_powerset.mp hW).trans hT) (fun U => F U W)

lemma powerset_sdiff_filter (S W : Finset ℕ) :
    (S \ W).powerset = S.powerset.filter (fun U => Disjoint U W) := by
  ext U
  simp only [mem_powerset, mem_filter]
  constructor
  · intro h
    exact ⟨fun p hp => (mem_sdiff.mp (h hp)).1,
      disjoint_left.mpr (fun p hp hpW => (mem_sdiff.mp (h hp)).2 hpW)⟩
  · rintro ⟨hU, hd⟩ p hp
    exact mem_sdiff.mpr ⟨hU hp, fun hpW => disjoint_left.mp hd hp hpW⟩

/-- The retained-prime product is the outer summation variable used in
the analytic transfer. Removed and retained primes are disjoint exactly. -/
theorem centerBand_reindex_retained (S T : Finset ℕ) (hT : T ⊆ S)
    (F : Finset ℕ → Finset ℕ → ℂ) :
    (∑ D ∈ S.powerset, ∑ W ∈ (D ∩ T).powerset, F (D \ W) W) =
      ∑ U ∈ S.powerset, ∑ W ∈ (T \ U).powerset, F U W := by
  rw [centerBand_reindex S T hT F]
  simp_rw [powerset_sdiff_filter, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro U _
  apply sum_congr rfl
  intro W _
  by_cases hd : Disjoint U W
  · simp only [hd, hd.symm, ite_true]
  · have hd' : ¬Disjoint W U := fun hw => hd hw.symm
    simp only [hd, hd', ite_false]

end TwoPointCorrelations

end OAI
