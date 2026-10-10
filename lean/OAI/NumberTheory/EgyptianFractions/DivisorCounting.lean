import OAI.NumberTheory.EgyptianFractions.Defs
import OAI.NumberTheory.EgyptianFractions.DivisorSplit
import OAI.NumberTheory.EgyptianFractions.FiniteExpansion

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A finite family of distinct denominator sets produces the same number of
increasing one-expansions. -/
lemma finset_family_card_le_F (family : Finset (Finset ℕ)) (k : ℕ)
    (hfinite : (OneExpansions k).Finite)
    (hfamily : ∀ s ∈ family, s.card = k ∧
      (∀ m ∈ s, 1 ≤ m) ∧ (∑ m ∈ s, (1 : ℚ) / m) = 1) :
    family.card ≤ F k := by
  classical
  have hex : ∀ s : family, ∃ n : Fin k → ℕ,
      IsOneExpansion n ∧ (∀ m, (∃ i, n i = m) ↔ m ∈ s.val) := by
    intro s
    obtain ⟨hc, hp, hs⟩ := hfamily s.val s.property
    have he := finset_unit_fraction_representation s.val 1 1 hp hs
    rw [hc] at he
    obtain ⟨n, hnp, hnm, hns, hnr⟩ := he
    exact ⟨n, ⟨hnp, hnm, hns⟩, hnr⟩
  let f : family → OneExpansions k := fun s =>
    ⟨Classical.choose (hex s), (Classical.choose_spec (hex s)).1⟩
  have hf : Function.Injective f := by
    intro s t hst
    have hn : Classical.choose (hex s) = Classical.choose (hex t) :=
      congrArg Subtype.val hst
    apply Subtype.ext
    apply Finset.ext
    intro m
    rw [← (Classical.choose_spec (hex s)).2 m,
      ← (Classical.choose_spec (hex t)).2 m, hn]
  let : Fintype (OneExpansions k) := hfinite.fintype
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Set.fintypeCard_eq_ncard, F] using hc

lemma countingDivisorSplitSet_positive {n d : ℕ} {s : Finset ℕ}
    (hd : d ∈ countingGoodSplitDivisors n s) (hs : ∀ m ∈ s, 1 ≤ m) :
    ∀ m ∈ countingDivisorSplitSet n d s, 1 ≤ m := by
  obtain ⟨hpos, hdvd, hlt, ha, hb⟩ := countingGoodSplitDivisors_spec hd
  have ho := divisorSplit_order hpos hdvd hlt
  intro m hm
  simp only [countingDivisorSplitSet, Finset.mem_insert] at hm
  rcases hm with rfl | rfl | hm
  · omega
  · omega
  · exact hs m hm

/-- Branching over all noncolliding proper divisors of one denominator. -/
theorem divisor_branching_lower_bound (s : Finset ℕ) (n : ℕ)
    (hn : n ∈ s) (hpos : ∀ m ∈ s, 1 ≤ m)
    (hsum : (∑ m ∈ s, (1 : ℚ) / m) = 1)
    (hfinite : (OneExpansions (s.card + 1)).Finite) :
    n.divisors.card - 1 - 2 * (s.card - 1) ≤ F (s.card + 1) := by
  classical
  let t := s.erase n
  let family := (countingGoodSplitDivisors n t).image (fun d => countingDivisorSplitSet n d t)
  have htcard : t.card = s.card - 1 := Finset.card_erase_of_mem hn
  have hcpos : 0 < s.card := Finset.card_pos.mpr ⟨n, hn⟩
  have htpos : ∀ m ∈ t, 1 ≤ m := fun m hm => hpos m (Finset.mem_of_mem_erase hm)
  have htsum : (∑ m ∈ t, (1 : ℚ) / m) + 1 / n = 1 := by
    exact (Finset.sum_erase_add s (fun m => (1 : ℚ) / m) hn).trans hsum
  have hf : family.card ≤ F (s.card + 1) := by
    apply finset_family_card_le_F family (s.card + 1) hfinite
    intro u hu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
    refine ⟨?_, countingDivisorSplitSet_positive hd htpos, ?_⟩
    · rw [countingDivisorSplitSet_card hd, htcard]
      omega
    · exact (countingDivisorSplitSet_sum hd).trans htsum
  have hfamily : family.card = (countingGoodSplitDivisors n t).card :=
    countingDivisorSplitSet_image_card n t
  have hl := countingGoodSplitDivisors_card_lower n t
  rw [htcard] at hl
  rw [hfamily] at hf
  exact hl.trans hf

end Problem337

end

end OAI
