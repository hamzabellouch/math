import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalEarlyUsedTest
import OAI.Combinatorics.BalancedRyser.Local.AlignedProjectedCollinearTest
import OAI.Combinatorics.BalancedRyser.Local.LocalExposureTiming
import OAI.Combinatorics.BalancedRyser.Local.LocalInjectionBudget

namespace OAI

namespace Balanced.Local
open RootChildPartition AlignedGlobal UsedEventUnion Timing
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem projected_collinear_rootsFirst_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hchild : ∀ i, i ∉ R → (P.classSet i ∩ R.biUnion P.classSet).card = 1)
    (bits : Bits b) (p : Point F) (hb : 10*b ≤ Fintype.card F)
    (i j k : Fin b × Fin 4)
    (hi : rootsFirstRank R i.1 < rootsFirstRank R k.1)
    (hj : rootsFirstRank R j.1 < rootsFirstRank R k.1)
    (hdep : k ∈ dependentOccurrences P R) :
    injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
      2 / (Fintype.card F : ℝ) := by
  by_cases hI : Nonempty (DirectionToken b κ ↪ Direction F)
  · let := hI
    let S := earlierTuples (rootsFirstRank R) k.1
    let K := prefixTokens P S
    exact collinearTest_injectionAverage_projected_le P hκ R S hD
      (rootsFirstRank_prefix R k.1) bits p i j k
      (by simpa [S,earlierTuples] using hi) (by simpa [S,earlierTuples] using hj)
      hdep (currentOldIndices_card_le_one P R hchild k.1)
      (currentOldIndices_in_prefix P R k.1) K
      (fun r hr => (inl_mem_prefixTokens P S r).mpr hr)
      (fun c hc => (inr_mem_prefixTokens P S c).mpr hc)
      (by simp [K,S,earlierTuples]) (card_token_set_le K) hb
  · let : IsEmpty (DirectionToken b κ ↪ Direction F) := ⟨fun e => hI ⟨e⟩⟩
    simp [injectionAverage]
    positivity

theorem projected_used_rootsFirst_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hchild : ∀ i, i ∉ R → (P.classSet i ∩ R.biUnion P.classSet).card = 1)
    (bits : Bits b) (p : Point F) (hb : 10*b ≤ Fintype.card F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool)
    (hdep : ij ∈ dependentOccurrences P R)
    (hc : c ∈ (earlierTuples (rootsFirstRank R) ij.1).biUnion P.classSet) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
      2 / (Fintype.card F : ℝ) := by
  by_cases hI : Nonempty (DirectionToken b κ ↪ Direction F)
  · let := hI
    let S := earlierTuples (rootsFirstRank R) ij.1
    let K := prefixTokens P S
    exact usedTest_injectionAverage_projected_le P hκ R S hD
      (rootsFirstRank_prefix R ij.1) bits p ij.1
      (currentOldIndices_card_le_one P R hchild ij.1)
      (currentOldIndices_in_prefix P R ij.1) ij.2 hdep K
      (fun r hr => (inl_mem_prefixTokens P S r).mpr hr)
      (fun d hd => (inr_mem_prefixTokens P S d).mpr hd)
      (by simp [K,S,earlierTuples]) c hc s (card_token_set_le K) hb
  · let : IsEmpty (DirectionToken b κ ↪ Direction F) := ⟨fun e => hI ⟨e⟩⟩
    simp [injectionAverage]
    positivity

theorem used_injectionAverage_le_two_div
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hchild : ∀ i, i ∉ R → (P.classSet i ∩ R.biUnion P.classSet).card = 1)
    (bits : Bits b) (p : Point F) (hb : 10*b ≤ Fintype.card F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
      2 / (Fintype.card F : ℝ) :=
  injectionAverage_usedTest_le_of_projected P hκ R hD bits p hb
    (projected_used_rootsFirst_le P hκ R hD hchild bits p hb) c ij s

theorem usedEventMean_le_two_reuses
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F)
    (hb : 3 ≤ b) (hbudget : 10*b ≤ Fintype.card F) :
    TwoReuseAssembly.usedEventMean P bits p ≤
      192 * (b : ℝ)^3 / Fintype.card F := by
  obtain ⟨R, _, _, hD, hchildren⟩ :=
    exists_roots_with_exact_dependent_budget P hb (by decide)
  have hchild : ∀ i, i ∉ R →
      (P.classSet i ∩ R.biUnion P.classSet).card = 1 :=
    fun i hi => (hchildren i hi).1
  apply usedEventMean_le_of_remaining_tests P R hD bits p (by omega)
  · exact used_injectionAverage_le_two_div P (by decide) R hD hchild bits p hbudget
  · exact projected_collinear_rootsFirst_le P (by decide) R hD hchild bits p hbudget

universe u

theorem injectiveUsedEventsEstimate_proof :
    TwoReuseAssembly.InjectiveUsedEventsEstimate.{u} := by
  obtain ⟨q₀, hq₀⟩ := exists_logBudget_token_threshold.{u}
  refine ⟨192, by norm_num, q₀, ?_⟩
  intro F _ _ _ hq b hb hB P bits p
  exact usedEventMean_le_two_reuses P bits p hb (hq₀ F hq b hB)

theorem pencilTwoReuses_proof : PencilTwoReusesResult.{u} :=
  TwoReuseAssembly.pencilTwoReuses_of_used_event_mean injectiveUsedEventsEstimate_proof

end
end Balanced.Local

end OAI
