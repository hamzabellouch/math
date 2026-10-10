import OAI.Combinatorics.BalancedRyser.Local.AlignedUsedTestTransport
import OAI.Combinatorics.BalancedRyser.Local.LocalInjectionLaw

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
open scoped BigOperators
open AlignedGlobal RootChildPartition
attribute [local instance] Classical.propDecidable

theorem uniform_product_probability_eq_mean {I Ω : Type*}
    [Fintype I] [Nonempty I] [Fintype Ω] [Nonempty Ω]
    (E : I → Ω → Prop) :
    ((PMF.uniformOfFintype (I × Ω)).toOuterMeasure {z | E z.1 z.2}).toReal =
      (∑ i, ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | E i ω}).toReal) /
        Fintype.card I := by
  rw [UniformConditionalProduct.uniform_product_eq_bind,
    uniform_bind_probability_eq_mean]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def injectionFreeProbability (P : EqualityPattern b κ) (R : Finset (Fin b))
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (G : (DirectionToken b κ ↪ Direction F) → (FreeIndex P R → F) → Prop) : ℝ :=
  ((PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) ×
    (FreeIndex P R → F))).toOuterMeasure {z | G z.1 z.2}).toReal

def injectedGenerated (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2 * κ)
    (bits : Bits b) (p : Point F) (e : DirectionToken b κ ↪ Direction F)
    (x : FreeIndex P R → F) : MergedPairs F :=
  generatedZero P hκ R hD (tokenInjectionEquiv F b κ e).1
    (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p x

theorem injectionAverage_le_injectionFreeProbability
    (P : EqualityPattern b κ) (R : Finset (Fin b)) (bits : Bits b) (p : Point F)
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (E : DirectionAssignment F b κ → MergedPairs F → Prop)
    (G : (DirectionToken b κ ↪ Direction F) → (FreeIndex P R → F) → Prop)
    (h : ∀ e : DirectionToken b κ ↪ Direction F,
      conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b κ e).1 bits p)
        (E (tokenInjectionEquiv F b κ e).1) ≤
      ((PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure {x | G e x}).toReal) :
    injectionAverage P bits p E ≤ injectionFreeProbability P R G := by
  unfold injectionFreeProbability injectionAverage
  rw [uniform_product_probability_eq_mean]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun e _ => h e))
    (Nat.cast_nonneg _)

theorem injectionAverage_eq_injectionFreeProbability
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2 * κ)
    (bits : Bits b) (p : Point F)
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (E : DirectionAssignment F b κ → MergedPairs F → Prop)
    (hE : ∀ a M N, (∀ d ∈ AlignedUnused.usedDirections P a, M d = N d) →
      (E a M ↔ E a N)) :
    injectionAverage P bits p E = injectionFreeProbability P R
      (fun e x => E (tokenInjectionEquiv F b κ e).1
        (injectedGenerated P hκ R hD bits p e x)) := by
  unfold injectionFreeProbability injectionAverage
  rw [uniform_product_probability_eq_mean (fun e x =>
    E (tokenInjectionEquiv F b κ e).1 (injectedGenerated P hκ R hD bits p e x))]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact conditioned_probability_eq_uniform_free P hκ R hD _
    (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p _
    (hE (tokenInjectionEquiv F b κ e).1)

theorem usedTest_injectionAverage_le_free
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2 * κ)
    (bits : Bits b) (p : Point F)
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (c : Fin (4 * b - κ)) (ij : Fin b × Fin 4) (s : Bool) :
    injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
      injectionFreeProbability P R (fun e x =>
        geometricUsedTest P (tokenInjectionEquiv F b κ e).1 bits p c ij s
          (injectedGenerated P hκ R hD bits p e x)) := by
  apply injectionAverage_le_injectionFreeProbability
  intro e
  exact conditioned_usedTest_le_uniform_free P hκ R hD _
    (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p c ij s

theorem collinearTest_injectionAverage_le_free
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2 * κ)
    (bits : Bits b) (p : Point F)
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (i j k : Fin b × Fin 4) :
    injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
      injectionFreeProbability P R (fun e x =>
        geometricCollinearTest P (tokenInjectionEquiv F b κ e).1 bits p i j k
          (injectedGenerated P hκ R hD bits p e x)) := by
  apply injectionAverage_le_injectionFreeProbability
  intro e
  exact conditioned_collinearTest_le_uniform_free P hκ R hD _
    (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p i j k

theorem usedEventMean_le_of_free_test_bounds
    (P : EqualityPattern b 2) (R : Finset (Fin b))
    (hD : (dependentOccurrences P R).card = 2 * 2)
    (bits : Bits b) (p : Point F) (hb : 1 ≤ b)
    [Nonempty (DirectionToken b 2 ↪ Direction F)]
    (hused : ∀ c ij s, injectionFreeProbability P R (fun e x =>
      geometricUsedTest P (tokenInjectionEquiv F b 2 e).1 bits p c ij s
        (injectedGenerated P (by decide) R hD bits p e x)) ≤
      2 / (Fintype.card F : ℝ))
    (htriple : ∀ i j k, injectionFreeProbability P R (fun e x =>
      geometricCollinearTest P (tokenInjectionEquiv F b 2 e).1 bits p i j k
        (injectedGenerated P (by decide) R hD bits p e x)) ≤
      2 / (Fintype.card F : ℝ)) :
    TwoReuseAssembly.usedEventMean P bits p ≤
      192 * (b : ℝ) ^ 3 / Fintype.card F := by
  apply usedEventMean_le_of_test_bounds P bits p hb
  · intro c ij s
    exact (usedTest_injectionAverage_le_free P (by decide) R hD bits p c ij s).trans
      (hused c ij s)
  · intro i j k
    exact (collinearTest_injectionAverage_le_free P (by decide) R hD bits p i j k).trans
      (htriple i j k)

end
end Balanced.Local.UsedEventUnion

end OAI
