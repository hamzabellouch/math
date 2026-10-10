import OAI.Combinatorics.BalancedRyser.Local.AlignedFreshHistory
import OAI.Combinatorics.BalancedRyser.Local.LocalTiming
import OAI.Combinatorics.BalancedRyser.Local.LocalUsedEventTiming

namespace OAI

namespace Balanced.Local.UsedEventUnion

open AlignedGlobal RootChildPartition
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem injectionAverage_le_const
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (E : DirectionAssignment F b κ → MergedPairs F → Prop)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ e : DirectionToken b κ ↪ Direction F,
      conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b κ e).1 bits p)
        (E (tokenInjectionEquiv F b κ e).1) ≤ C) :
    injectionAverage P bits p E ≤ C := by
  have hm := TwoReuseAssembly.mean_le_mean_add
    (fun e : DirectionToken b κ ↪ Direction F =>
      conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b κ e).1 bits p)
        (E (tokenInjectionEquiv F b κ e).1)) (fun _ => 0) C hC
    (fun e => by simpa using h e)
  simpa [injectionAverage] using hm

theorem injectionAverage_fresh_usedTest_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (v : FreeIndex P R) (hv : v.1.1 ∉ S)
    (c : Fin (4*b-κ)) (hc : c ∈ S.biUnion P.classSet) (s : Bool) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c v.1 s) ≤
      1 / (Fintype.card F : ℝ) := by
  apply injectionAverage_le_const P bits p _ _ (by positivity)
  intro e
  exact conditioned_fresh_usedTest_le P hκ R S hD hS _
    (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2)
    bits p v hv c hc s

theorem injectionAverage_fresh_collinearTest_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S) (bits : Bits b) (p : Point F)
    (v : FreeIndex P R) (hv : v.1.1 ∉ S)
    (i j : Fin b × Fin 4) (hi : i.1 ∈ S) (hj : j.1 ∈ S) :
    injectionAverage P bits p (fun a => collinearTest P a bits p i j v.1) ≤
      1 / (Fintype.card F : ℝ) := by
  apply injectionAverage_le_const P bits p _ _ (by positivity)
  intro e
  exact conditioned_fresh_collinearTest_le P hκ R S hD hS _
    (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2)
    bits p v hv i j hi hj

theorem collinear_injectionAverage_le_of_projected_latest
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F)
    (rank : Fin b → ℕ) (hrank : Function.Injective rank)
    (hphase : ∀ k : Fin b,
      (Finset.univ.filter (fun t => rank t < rank k)) ⊆ R ∨
      R ⊆ (Finset.univ.filter (fun t => rank t < rank k)))
    (hprojected : ∀ i j k : Fin b × Fin 4,
      rank i.1 < rank k.1 → rank j.1 < rank k.1 →
      k ∈ dependentOccurrences P R →
      injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
        2 / (Fintype.card F : ℝ))
    (i j k : Fin b × Fin 4) :
    injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
      2 / (Fintype.card F : ℝ) := by
  classical
  apply collinear_injectionAverage_le_of_latest P bits p rank hrank _ (by positivity) _ i j k
  intro i j k hi hj
  by_cases hk : k ∈ dependentOccurrences P R
  · exact hprojected i j k hi hj hk
  · have hf := injectionAverage_fresh_collinearTest_le P hκ R
      (Finset.univ.filter (fun t => rank t < rank k.1)) hD (hphase k.1)
      bits p ⟨k,hk⟩ (by simp) i j (by simpa using hi) (by simpa using hj)
    exact hf.trans (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _))

theorem usedEventMean_le_of_remaining_tests
    (P : EqualityPattern b 2) (R : Finset (Fin b))
    (hD : (dependentOccurrences P R).card = 2*2)
    (bits : Bits b) (p : Point F) (hb : 1 ≤ b)
    (hused : ∀ c ij s,
      injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
        2 / (Fintype.card F : ℝ))
    (hprojected : ∀ i j k : Fin b × Fin 4,
      Timing.rootsFirstRank R i.1 < Timing.rootsFirstRank R k.1 →
      Timing.rootsFirstRank R j.1 < Timing.rootsFirstRank R k.1 →
      k ∈ dependentOccurrences P R →
      injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
        2 / (Fintype.card F : ℝ)) :
    TwoReuseAssembly.usedEventMean P bits p ≤
      192 * (b : ℝ)^3 / Fintype.card F := by
  apply usedEventMean_le_of_test_bounds P bits p hb hused
  intro i j k
  exact collinear_injectionAverage_le_of_projected_latest P (by decide) R hD
    bits p (Timing.rootsFirstRank R) (Timing.rootsFirstRank_injective R)
    (Timing.rootsFirstRank_prefix R) hprojected i j k

end
end Balanced.Local.UsedEventUnion

end OAI
