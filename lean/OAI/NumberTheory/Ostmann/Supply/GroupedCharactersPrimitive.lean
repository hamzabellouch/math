import OAI.NumberTheory.Ostmann.Supply.GroupedCharactersExpBound
import OAI.NumberTheory.Ostmann.Supply.GroupedCharactersFamily
import OAI.NumberTheory.Ostmann.Supply.GroupedPrimitiveCharacters

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedCharacters
open Finset Ostmann.ZeroDensity
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp : Function.Injective p)
  (K pmax : ℕ) (hmax : 1 ≤ pmax) (hbound : ∀ i, p i ≤ pmax)
local instance (i : ι) : Fintype (DirichletCharacter ℂ (p i)) := Fintype.ofFinite _

def boundedCharacter (ρ : supportedCharacters (fun i => ZMod (p i)) K) :
    PrimitiveFamily (pmax^(2*K)) :=
  primitivePairToFamily (pmax^(2*K)) (GroupedPrimitiveCharacters.primitivePair p ρ.val)
    (GroupedPrimitiveCharacters.primitivePair_pos p ρ.val) (by
      rw [GroupedPrimitiveCharacters.primitivePair_fst p hp]
      calc
        _ ≤ ∏ i ∈ characterSupport (fun i => ZMod (p i)) ρ.val, pmax :=
          prod_le_prod (fun i hi => hbound i)
        _ = pmax^((characterSupport (fun i => ZMod (p i)) ρ.val).card) := prod_const _
        _ ≤ _ := pow_le_pow_right' hmax (mem_filter.mp ρ.property).2)

theorem boundedCharacter_injective : Function.Injective (boundedCharacter p hp K pmax hmax hbound) := by
  intro ρ σ he
  apply Subtype.ext
  apply GroupedPrimitiveCharacters.primitivePair_injective p hp
  have hh := congrArg familyToPrimitivePair he
  simpa only [boundedCharacter, familyToPrimitivePair_toFamily] using hh

theorem boundedCharacter_conductor (ρ : supportedCharacters (fun i => ZMod (p i)) K) :
    (boundedCharacter p hp K pmax hmax hbound ρ).1.val+1 =
      ∏ i ∈ characterSupport (fun i => ZMod (p i)) ρ.val, p i := by
  rw [boundedCharacter, primitivePairToFamily_conductor, GroupedPrimitiveCharacters.primitivePair_fst p hp]

theorem boundedCharacter_apply (ρ : supportedCharacters (fun i => ZMod (p i)) K)
    (n : ℕ) (hn : ∀ i, Nat.Coprime n (p i)) :
    (boundedCharacter p hp K pmax hmax hbound ρ).2.1 n = ∏ i, ρ.val i (n : ZMod (p i)) := by
  rw [boundedCharacter, primitivePairToFamily_apply]
  exact GroupedPrimitiveCharacters.primitivePair_apply_nat p ρ.val n hn

def primitiveCoefficient (b : ∀ i, ZMod (p i) → ℝ) (χ : PrimitiveFamily (pmax^(2*K))) : ℂ :=
  groupedCoefficient univ (boundedCharacter p hp K pmax hmax hbound)
    (fun ρ => weightCoefficient (fun i => ZMod (p i)) b K ρ.val) χ

theorem grouped_sum_univ {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (s : Finset α) (e : α → β) (c : α → ℂ) (he : Set.InjOn e (s : Set α)) (f : β → ℂ) :
    (∑ χ : β, groupedCoefficient s e c χ * f χ) = ∑ i ∈ s, c i * f (e i) := by
  calc
    _ = ∑ χ ∈ s.image e, groupedCoefficient s e c χ * f χ := by
      symm
      apply sum_subset (subset_univ _)
      intro χ hχ hnot
      rw [groupedCoefficient_not_mem s e c hnot, zero_mul]
    _ = _ := grouped_sum s e c he f

theorem primitive_weight_expansion (b : ∀ i, ZMod (p i) → ℝ) (n : ℕ)
    (hn : ∀ i, Nat.Coprime n (p i)) :
    (truncatedWeight univ (fun i => b i (n : ZMod (p i))) K : ℂ) =
      ∑ χ : PrimitiveFamily (pmax^(2*K)), primitiveCoefficient p hp K pmax hmax hbound b χ * χ.2.1 n := by
  rw [localWeight_expansion_nat p b K n hn]
  symm
  simp only [primitiveCoefficient]
  rw [grouped_sum_univ _ _ _ (boundedCharacter_injective p hp K pmax hmax hbound).injOn]
  simp only [boundedCharacter_apply p hp K pmax hmax hbound _ n hn]
  exact sum_coe_sort (supportedCharacters (fun i => ZMod (p i)) K)
    (fun ρ => weightCoefficient (fun i => ZMod (p i)) b K ρ * ∏ i, ρ i (n : ZMod (p i)))

def principalTuple : supportedCharacters (fun i => ZMod (p i)) K :=
  ⟨1, by simp [supportedCharacters, characterSupport]⟩

def principalCharacter : PrimitiveFamily (pmax^(2*K)) :=
  ⟨⟨0, pow_pos (by omega : 0 < pmax) _⟩, 1, DirichletCharacter.isPrimitive_one_level_one⟩

theorem boundedCharacter_principal :
    boundedCharacter p hp K pmax hmax hbound (principalTuple p K) = principalCharacter K pmax hmax := by
  apply familyToPrimitivePair_injective
  rw [boundedCharacter, familyToPrimitivePair_toFamily]
  exact GroupedPrimitiveCharacters.primitivePair_one p

theorem primitiveCoefficient_principal (b : ∀ i, ZMod (p i) → ℝ) :
    primitiveCoefficient p hp K pmax hmax hbound b (principalCharacter K pmax hmax) =
      weightCoefficient (fun i => ZMod (p i)) b K 1 := by
  rw [← boundedCharacter_principal p hp K pmax hmax hbound]
  exact groupedCoefficient_image univ _ _ (boundedCharacter_injective p hp K pmax hmax hbound).injOn
    (mem_univ (principalTuple p K))

end Ostmann.Supply.GroupedCharacters

end

end OAI
