import OAI.NumberTheory.Ostmann.Supply.GroupedPrimitiveCharactersConductor

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedPrimitiveCharacters
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def modulus (p : ι → ℕ) : ℕ := ∏ i, p i

omit [DecidableEq ι] in
theorem dvd_modulus (p : ι → ℕ) (i : ι) : p i ∣ modulus p :=
  Finset.dvd_prod_of_mem p (Finset.mem_univ i)

instance modulus_neZero (p : ι → ℕ) [∀ i, Fact (p i).Prime] : NeZero (modulus p) := by
  constructor
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (Fact.out : (p i).Prime).ne_zero

def localLift (p : ι → ℕ) (i : ι) (ρ : DirichletCharacter ℂ (p i)) :
    DirichletCharacter ℂ (modulus p) :=
  DirichletCharacter.changeLevel (dvd_modulus p i) ρ

def fullCharacter (p : ι → ℕ) (ρ : ∀ i, DirichletCharacter ℂ (p i)) :
    DirichletCharacter ℂ (modulus p) := ∏ i, localLift p i (ρ i)

def fullCharacterHom (p : ι → ℕ) :
    (∀ i, DirichletCharacter ℂ (p i)) →* DirichletCharacter ℂ (modulus p) where
  toFun := fullCharacter p
  map_one' := by simp [fullCharacter, localLift]
  map_mul' ρ σ := by simp [fullCharacter, localLift, Finset.prod_mul_distrib]

omit [DecidableEq ι] in
theorem fullCharacter_div (p : ι → ℕ) (ρ σ : ∀ i, DirichletCharacter ℂ (p i)) :
    fullCharacter p (ρ/σ) = fullCharacter p ρ / fullCharacter p σ :=
  map_div (fullCharacterHom p) ρ σ

theorem mulChar_prod_apply_unit {α : Type*} [DecidableEq α] {N : ℕ}
    (s : Finset α) (χ : α → DirichletCharacter ℂ N) (x : (ZMod N)ˣ) :
    (∏ i ∈ s, χ i) (x : ZMod N) = ∏ i ∈ s, χ i (x : ZMod N) := by
  induction s using Finset.induction_on with
  | empty => simp [MulChar.one_apply_coe]
  | @insert a s ha ih => simp only [Finset.prod_insert ha, MulChar.mul_apply, ih]

theorem fullCharacter_apply_unit (p : ι → ℕ) (ρ : ∀ i, DirichletCharacter ℂ (p i))
    (x : (ZMod (modulus p))ˣ) :
    fullCharacter p ρ (x : ZMod (modulus p)) =
      ∏ i, ρ i (ZMod.cast (x : ZMod (modulus p))) := by
  rw [fullCharacter, mulChar_prod_apply_unit]
  apply Finset.prod_congr rfl
  intro i _
  exact DirichletCharacter.changeLevel_eq_cast_of_dvd (ρ i) (dvd_modulus p i) x

theorem fullCharacter_apply_nat (p : ι → ℕ) (ρ : ∀ i, DirichletCharacter ℂ (p i))
    (n : ℕ) (hn : ∀ i, Nat.Coprime n (p i)) :
    fullCharacter p ρ (n : ZMod (modulus p)) = ∏ i, ρ i (n : ZMod (p i)) := by
  have hnQ : Nat.Coprime n (modulus p) := Nat.coprime_fintype_prod_right_iff.mpr hn
  simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast (dvd_modulus p _)] using
    fullCharacter_apply_unit p ρ (ZMod.unitOfCoprime n hnQ)

end Ostmann.Supply.GroupedPrimitiveCharacters

end

end OAI
