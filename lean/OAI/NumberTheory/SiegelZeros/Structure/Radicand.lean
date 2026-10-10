import OAI.NumberTheory.SiegelZeros.Characters.CharacterFrobenius
import OAI.NumberTheory.SiegelZeros.Characters.ExceptionalConductor
import OAI.NumberTheory.SiegelZeros.Characters.GaussSquarefreeBridge

namespace OAI

namespace SiegelZeros


namespace W56

open SiegelZerosAwei.W09 SiegelZerosAwei.W38
open scoped NumberField

theorem conductor_eight_of_signedConductor_twice_square
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq1 : q ≠ 1) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (k : ℤ) (hD : signedConductor χ = 2 * k ^ 2) : q = 8 := by
  apply conductor_eight_of_prime_values χ hq1 hprim
  intro p hp hp2 hpq
  let : Fact p.Prime := ⟨hp⟩
  let := complexCyclotomicField_isCyclotomic (q := q)
  let : FiniteDimensional ℚ (complexCyclotomicField q) :=
    IsCyclotomicExtension.finiteDimensional {q} ℚ (complexCyclotomicField q)
  let : NumberField (complexCyclotomicField q) := ⟨⟩
  rw [Awei.W39.character_legendre_radicand_of_residue p hp2 hpq χ hprim hquad
    (primeReduction (complexCyclotomicField q) p) 2 k hD,
    legendreSym.at_two hp2]

theorem reduced_radicand_ne_two
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq1 : q ≠ 1) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic) (hq8 : q ≠ 8)
    (d k : ℤ) (hD : signedConductor χ = k ^ 2 * d) : d ≠ 2 := by
  intro hd
  apply hq8
  apply conductor_eight_of_signedConductor_twice_square χ hq1 hprim hquad k
  simpa [hd, mul_comm] using hD

theorem characterField_squarefree_radicand_nonexceptional
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq1 : q ≠ 1) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (hn : χ ≠ 1) (hq8 : q ≠ 8) :
    ∃ (d k : ℤ) (b : ℂ), Squarefree d ∧ d ≠ 1 ∧ d ≠ 2 ∧ k ≠ 0 ∧
      signedConductor χ = k ^ 2 * d ∧ d.natAbs ≤ q ∧
      b = characterGaussSum χ / (k : ℂ) ∧ b ^ 2 = (d : ℂ) ∧
      IntermediateField.adjoin ℚ ({b} : Set ℂ) = characterField χ := by
  obtain ⟨d, k, b, hd, hd1, hk, hD, hbound, hbdef, hb, hf⟩ :=
    characterField_squarefree_radicand χ hprim hquad hn
  exact ⟨d, k, b, hd, hd1, reduced_radicand_ne_two χ hq1 hprim hquad hq8 d k hD,
    hk, hD, hbound, hbdef, hb, hf⟩

end W56



namespace Awei.W39
open SiegelZerosAwei.W09 _root_.OAI.SiegelZeros.W56

theorem actual_squarefree_radicand_with_prime_signs
    {q : ℕ} [NeZero q] (hq3 : 3 ≤ q) (hq8 : q ≠ 8)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hreal : IsRealCharacter χ) (hn : χ ≠ 1) :
    ∃ (d k : ℤ) (b : ℂ), Squarefree d ∧ d ≠ 1 ∧ d ≠ 2 ∧ k ≠ 0 ∧
      signedConductor χ = k ^ 2 * d ∧ d.natAbs ≤ q ∧
      b = characterGaussSum χ / (k : ℂ) ∧ b ^ 2 = (d : ℂ) ∧
      IntermediateField.adjoin ℚ ({b} : Set ℂ) = characterField χ ∧
      ∀ (p : ℕ) (hp : p.Prime), p ≠ 2 → ¬ p ∣ q →
        χ (p : ZMod q) = (@legendreSym p ⟨hp⟩ d : ℂ) := by
  have hq1 : q ≠ 1 := ne_of_gt (lt_of_lt_of_le (by decide : 1 < 3) hq3)
  have hquad := realCharacter_isQuadratic χ hreal
  obtain ⟨d, k, b, hd, hd1, hd2, hk, hD, hbound, hbdef, hb, hf⟩ :=
    characterField_squarefree_radicand_nonexceptional χ hq1 hprim hquad hn hq8
  refine ⟨d, k, b, hd, hd1, hd2, hk, hD, hbound, hbdef, hb, hf, ?_⟩
  intro p hp hp2 hpq
  let : Fact p.Prime := ⟨hp⟩
  exact character_legendre_radicand p hp2 hpq χ hprim hquad d k hD

end Awei.W39


end SiegelZeros

end OAI
