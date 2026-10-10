import OAI.NumberTheory.Ostmann.Supply.GroupedCharactersSupport
import OAI.NumberTheory.Ostmann.Supply.GroupedPrimitiveCharactersLift

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedPrimitiveCharacters
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime]

theorem fullCharacter_conductor (hp : Function.Injective p)
    (ρ : ∀ i, DirichletCharacter ℂ (p i)) :
    (fullCharacter p ρ).conductor =
      ∏ i ∈ GroupedCharacters.characterSupport (fun i => ZMod (p i)) ρ, p i := by
  have hcop : ((Finset.univ : Finset ι) : Set ι).Pairwise
      (fun i j => Nat.Coprime (localLift p i (ρ i)).conductor (localLift p j (ρ j)).conductor) := by
    intro i _ j _ hij
    simp only [localLift, DirichletCharacter.conductor_changeLevel]
    have hprimes : Nat.Coprime (p i) (p j) :=
      (Nat.coprime_primes (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mpr
        (fun h => hij (hp h))
    exact hprimes.of_dvd (ρ i).conductor_dvd_level (ρ j).conductor_dvd_level
  calc
    _ = ∏ i, (localLift p i (ρ i)).conductor :=
      conductor_prod_of_pairwise Finset.univ (fun i => localLift p i (ρ i)) hcop
    _ = ∏ i, if ρ i = 1 then 1 else p i := by
      apply Finset.prod_congr rfl
      intro i _
      rw [localLift, DirichletCharacter.conductor_changeLevel, conductor_prime]
    _ = _ := by
      simp only [GroupedCharacters.characterSupport, Finset.prod_filter, ite_not]

theorem fullCharacter_eq_one_iff (hp : Function.Injective p)
    (ρ : ∀ i, DirichletCharacter ℂ (p i)) : fullCharacter p ρ = 1 ↔ ρ = 1 := by
  constructor
  · intro h
    have hprod := congrArg (fun χ : DirichletCharacter ℂ (modulus p) => χ.conductor) h
    rw [fullCharacter_conductor p hp, DirichletCharacter.conductor_one] at hprod
    funext i
    change ρ i = 1
    by_contra hi
    have hmem : i ∈ GroupedCharacters.characterSupport (fun i => ZMod (p i)) ρ :=
      (GroupedCharacters.mem_characterSupport _ ρ i).mpr hi
    have hdvd := Finset.dvd_prod_of_mem p hmem
    rw [hprod] at hdvd
    exact (Fact.out : (p i).Prime).not_dvd_one hdvd
  · intro h
    rw [h]
    exact (fullCharacterHom p).map_one

theorem fullCharacter_injective (hp : Function.Injective p) :
    Function.Injective (fullCharacter p) := by
  intro ρ σ he
  have hdiv : fullCharacter p (ρ/σ) = 1 := by
    rw [fullCharacter_div, he, div_self']
  exact div_eq_one.mp ((fullCharacter_eq_one_iff p hp (ρ/σ)).mp hdiv)

end Ostmann.Supply.GroupedPrimitiveCharacters

end

end OAI
