import OAI.NumberTheory.Ostmann.Supply.GroupedCharactersBound
import OAI.NumberTheory.Ostmann.Supply.GroupedCharactersSupport

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedCharacters
open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
local instance (i : ι) : Fintype (MulChar (F i) ℂ) := Fintype.ofFinite _

def supportedCharacters (K : ℕ) : Finset (∀ i, MulChar (F i) ℂ) :=
  univ.filter (fun ρ => (characterSupport F ρ).card ≤ 2*K)

theorem weight_expansion_supported (b : ∀ i, F i → ℝ) (K : ℕ) (x : ∀ i, (F i)ˣ) :
    (truncatedWeight univ (fun i => b i (x i)) K : ℂ) =
      ∑ ρ ∈ supportedCharacters F K, weightCoefficient F b K ρ * unitCharacter F ρ x := by
  rw [weight_expansion F b K x, supportedCharacters, sum_filter]
  apply sum_congr rfl
  intro ρ hρ
  by_cases h : (characterSupport F ρ).card ≤ 2*K
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, weightCoefficient_eq_zero_of_card F b K ρ (by omega), zero_mul]

section Naturals
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime]

theorem localWeight_expansion_nat (b : ∀ i, ZMod (p i) → ℝ) (K n : ℕ)
    (hn : ∀ i, Nat.Coprime n (p i)) :
    (truncatedWeight univ (fun i => b i (n : ZMod (p i))) K : ℂ) =
      ∑ ρ ∈ supportedCharacters (fun i => ZMod (p i)) K,
        weightCoefficient (fun i => ZMod (p i)) b K ρ * ∏ i, ρ i (n : ZMod (p i)) := by
  simpa only [unitCharacter, ZMod.coe_unitOfCoprime] using
    weight_expansion_supported (fun i => ZMod (p i)) b K (fun i => ZMod.unitOfCoprime n (hn i))

theorem actual_localWeight_expansion_nat (S : ∀ i, Finset (ZMod (p i))) (K n : ℕ)
    (hn : ∀ i, Nat.Coprime n (p i)) :
    (truncatedWeight univ (fun i => localKernel (S i) sparseKernelScale (n : ZMod (p i))) K : ℂ) =
      ∑ ρ ∈ supportedCharacters (fun i => ZMod (p i)) K,
        weightCoefficient (fun i => ZMod (p i)) (fun i => localKernel (S i) sparseKernelScale) K ρ *
          ∏ i, ρ i (n : ZMod (p i)) :=
  localWeight_expansion_nat p _ K n hn

end Naturals
end Ostmann.Supply.GroupedCharacters

end

end OAI
