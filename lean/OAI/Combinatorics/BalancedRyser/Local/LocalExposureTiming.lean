import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalCurrentTuple
import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalGeneratorTest
import OAI.Combinatorics.BalancedRyser.Local.LocalTiming
import OAI.Combinatorics.BalancedRyser.Local.LocalUsedFreshMean

namespace OAI

namespace Balanced.Local.Timing
open RootChildPartition AlignedGlobal UsedEventUnion
noncomputable section
open scoped Classical
variable {b κ : ℕ}

def prefixTokens (P : EqualityPattern b κ) (S : Finset (Fin b)) :
    Finset (DirectionToken b κ) :=
  S.image Sum.inl ∪ (S.biUnion P.classSet).image Sum.inr

@[simp] theorem inl_mem_prefixTokens (P : EqualityPattern b κ)
    (S : Finset (Fin b)) (i : Fin b) :
    Sum.inl i ∈ prefixTokens P S ↔ i ∈ S := by
  simp [prefixTokens]

@[simp] theorem inr_mem_prefixTokens (P : EqualityPattern b κ)
    (S : Finset (Fin b)) (c : Fin (4*b-κ)) :
    Sum.inr c ∈ prefixTokens P S ↔ c ∈ S.biUnion P.classSet := by
  simp [prefixTokens]

theorem card_token_set_le (K : Finset (DirectionToken b κ)) : K.card ≤ 5*b := by
  have h := Finset.card_le_univ K
  simp only [DirectionToken, Fintype.card_sum, Fintype.card_fin] at h
  omega

theorem rootsFirstRank_phase (R : Finset (Fin b)) (i : Fin b) :
    i ∈ R ∨ R ⊆ earlierTuples (rootsFirstRank R) i := by
  by_cases hi : i ∈ R
  · exact Or.inl hi
  · right
    intro j hj
    simp only [earlierTuples, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [rootsFirstRank, hi, hj, ite_true, ite_false]
    omega

theorem currentOldIndices_in_prefix (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (i : Fin b) :
    ∀ j ∈ currentOldIndices P R i,
      P.classOf i j ∈ (earlierTuples (rootsFirstRank R) i).biUnion P.classSet := by
  intro j hj
  by_cases hi : i ∈ R
  · simp [currentOldIndices, hi] at hj
  · have hc : P.classOf i j ∈ R.biUnion P.classSet := by
      simpa [currentOldIndices, hi, rootGeneratorIndices] using hj
    obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨r,
      (rootsFirstRank_phase R i).resolve_left hi hr, hcr⟩

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem injectionAverage_later_usedTest_le
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (first : Fin b) (j : Fin 4)
    (hnew : P.classOf first j ∉
      (earlierTuples (rootsFirstRank R) first).biUnion P.classSet)
    (ij : Fin b × Fin 4)
    (hearlier : rootsFirstRank R ij.1 < rootsFirstRank R first)
    (s : Bool) (hb : 10*b ≤ Fintype.card F) :
    injectionAverage P bits p
      (fun a => usedConstituentTest P a bits p (P.classOf first j) ij s) ≤
        2 / (Fintype.card F : ℝ) := by
  let S := earlierTuples (rootsFirstRank R) first
  let K := insert (Sum.inl first) (prefixTokens P S)
  have hr : ij.1 ∈ S := by simpa [S, earlierTuples] using hearlier
  apply (usedTest_injectionAverage_le_free P hκ R hD bits p
    (P.classOf first j) ij s).trans
  exact geometricUsedTest_later_generator_le P hκ R S hD
    (rootsFirstRank_prefix R first) bits p first (rootsFirstRank_phase R first) K
    (fun r hr => Finset.mem_insert_of_mem ((inl_mem_prefixTokens P S r).mpr hr))
    (fun c hc => Finset.mem_insert_of_mem ((inr_mem_prefixTokens P S c).mpr hc))
    (Finset.mem_insert_self _ _) j (by simpa [K, S] using hnew)
    s ⟨ij.1,hr⟩ ij.2 (card_token_set_le K) hb

theorem injectionAverage_usedTest_le_of_projected
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (hb : 10*b ≤ Fintype.card F)
    (hprojected : ∀ (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool),
      ij ∈ dependentOccurrences P R →
      c ∈ (earlierTuples (rootsFirstRank R) ij.1).biUnion P.classSet →
      injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
        2 / (Fintype.card F : ℝ))
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
      2 / (Fintype.card F : ℝ) := by
  by_cases hI : Nonempty (DirectionToken b κ ↪ Direction F)
  · let := hI
    by_cases hnot : ∀ j, P.classOf ij.1 j ≠ c
    · obtain ⟨first, j, hc, hnew, horder⟩ := exists_first_class_use_timing
        P (rootsFirstRank R) (rootsFirstRank_injective R) c ij.1 hnot
      rcases horder with hearly | hlater
      · have hcfirst : c ∈ P.classSet first :=
          Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hc⟩
        have hcS : c ∈ (earlierTuples (rootsFirstRank R) ij.1).biUnion P.classSet :=
          (mem_earlier_classes_iff_first_use P (rootsFirstRank R) c first ij.1
            hcfirst hnew).mpr hearly
        by_cases hdep : ij ∈ dependentOccurrences P R
        · exact hprojected c ij s hdep hcS
        · exact (injectionAverage_fresh_usedTest_le P hκ R
            (earlierTuples (rootsFirstRank R) ij.1) hD
            (rootsFirstRank_prefix R ij.1) bits p ⟨ij,hdep⟩
            (by simp [earlierTuples]) c hcS s).trans
              (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _))
      · have hn : P.classOf first j ∉
            (earlierTuples (rootsFirstRank R) first).biUnion P.classSet := by
          simpa only [hc] using hnew
        simpa only [hc] using injectionAverage_later_usedTest_le
          P hκ R hD bits p first j hn ij hlater s hb
    · simp [injectionAverage, conditionedOffsetProbability, offsetProbability,
        usedConstituentTest, hnot]
      positivity
  · let : IsEmpty (DirectionToken b κ ↪ Direction F) := ⟨fun e => hI ⟨e⟩⟩
    simp [injectionAverage]
    positivity

end
end Balanced.Local.Timing

end OAI
