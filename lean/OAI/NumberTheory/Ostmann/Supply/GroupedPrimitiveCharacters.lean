import OAI.NumberTheory.Ostmann.Supply.GroupedPrimitiveCharactersProduct

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedPrimitiveCharacters
open scoped BigOperators

abbrev PrimitivePair := Σ q : ℕ, {χ : DirichletCharacter ℂ q // χ.IsPrimitive}

def principalPair : PrimitivePair :=
  ⟨1, ⟨1, DirichletCharacter.isPrimitive_one_level_one⟩⟩

def inducePair (Q : ℕ) (χ : PrimitivePair) : DirichletCharacter ℂ Q :=
  if h : χ.1 ∣ Q then DirichletCharacter.changeLevel h χ.2.val else 1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primitivePair (p : ι → ℕ) (ρ : ∀ i, DirichletCharacter ℂ (p i)) : PrimitivePair :=
  ⟨(fullCharacter p ρ).conductor,
    ⟨(fullCharacter p ρ).primitiveCharacter, (fullCharacter p ρ).primitiveCharacter_isPrimitive⟩⟩

omit [DecidableEq ι] in
theorem inducePair_primitivePair (p : ι → ℕ) (ρ : ∀ i, DirichletCharacter ℂ (p i)) :
    inducePair (modulus p) (primitivePair p ρ) = fullCharacter p ρ := by
  unfold inducePair primitivePair
  split
  · exact (fullCharacter p ρ).changeLevel_primitiveCharacter
  · rename_i h
    exact False.elim (h (fullCharacter p ρ).conductor_dvd_level)

theorem primitivePair_injective (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hp : Function.Injective p) : Function.Injective (primitivePair p) := by
  intro ρ σ he
  apply fullCharacter_injective p hp
  simpa only [inducePair_primitivePair] using congrArg (inducePair (modulus p)) he

theorem primitivePair_fst (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hp : Function.Injective p) (ρ : ∀ i, DirichletCharacter ℂ (p i)) :
    (primitivePair p ρ).1 =
      ∏ i ∈ GroupedCharacters.characterSupport (fun i => ZMod (p i)) ρ, p i :=
  fullCharacter_conductor p hp ρ

omit [DecidableEq ι] in
theorem primitivePair_pos (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (ρ : ∀ i, DirichletCharacter ℂ (p i)) : 0 < (primitivePair p ρ).1 :=
  Nat.pos_of_ne_zero (fullCharacter p ρ).conductor_ne_zero

theorem primitivePair_apply_nat (p : ι → ℕ) (ρ : ∀ i, DirichletCharacter ℂ (p i))
    (n : ℕ) (hn : ∀ i, Nat.Coprime n (p i)) :
    (primitivePair p ρ).2.val (n : ZMod (primitivePair p ρ).1) =
      ∏ i, ρ i (n : ZMod (p i)) := by
  have hnQ : Nat.Coprime n (modulus p) := Nat.coprime_fintype_prod_right_iff.mpr hn
  have he := DirichletCharacter.changeLevel_eq_cast_of_dvd
    (fullCharacter p ρ).primitiveCharacter (fullCharacter p ρ).conductor_dvd_level
    (ZMod.unitOfCoprime n hnQ)
  rw [(fullCharacter p ρ).changeLevel_primitiveCharacter] at he
  simp only [ZMod.coe_unitOfCoprime,
    ZMod.cast_natCast (fullCharacter p ρ).conductor_dvd_level] at he
  exact he.symm.trans (fullCharacter_apply_nat p ρ n hn)

theorem pair_eq_principal_of_fst_eq_one (χ : PrimitivePair) (hχ : χ.1 = 1) :
    χ = principalPair := by
  rcases χ with ⟨q, χ, hprim⟩
  dsimp at hχ
  subst q
  have he : (⟨χ, hprim⟩ : {χ : DirichletCharacter ℂ 1 // χ.IsPrimitive}) =
      ⟨1, DirichletCharacter.isPrimitive_one_level_one⟩ :=
    Subtype.ext (DirichletCharacter.level_one χ)
  exact congrArg (fun x => (Sigma.mk 1 x : PrimitivePair)) he

omit [DecidableEq ι] in
theorem primitivePair_one (p : ι → ℕ) [∀ i, Fact (p i).Prime] :
    primitivePair p (1 : ∀ i, DirichletCharacter ℂ (p i)) = principalPair := by
  apply pair_eq_principal_of_fst_eq_one
  change (fullCharacter p 1).conductor = 1
  rw [show fullCharacter p 1 = 1 from (fullCharacterHom p).map_one,
    DirichletCharacter.conductor_one]

theorem primitivePair_eq_principal_iff (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hp : Function.Injective p) (ρ : ∀ i, DirichletCharacter ℂ (p i)) :
    primitivePair p ρ = principalPair ↔ ρ = 1 := by
  rw [← primitivePair_one p]
  exact ⟨fun h => primitivePair_injective p hp h, fun h => congrArg (primitivePair p) h⟩

end Ostmann.Supply.GroupedPrimitiveCharacters

end

end OAI
