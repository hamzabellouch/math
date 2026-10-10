import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Determinants.SqrtPairFrobeniusDirections
import OAI.NumberTheory.SiegelZeros.Structure.SumLogDivFilterDvdTwoMul

namespace OAI

namespace SiegelZeros

open scoped BigOperators

namespace WeightedTorusJets

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem exists_auxiliary_sqrt_pair_with_characterField (q : ℕ) [NeZero q]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L]
    [NeZero (8 * q)] [IsAbelianGalois ℚ L]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) (hq8 : q ≠ 8) :
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IsIntegral ℤ a ∧ IsIntegral ℤ b ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b} ∧
      ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q →
        ∀ (P : Ideal (𝓞 L)), P.under ℤ = Ideal.span {(p : ℤ)} →
          ∀ (σ : Gal(L/ℚ)), IsArithFrobAt ℤ σ P → χ p = -1 → σ a = -a := by
  have hqm : q ∣ 8 * q := dvd_mul_left q 8
  have h8m : 8 ∣ 8 * q := dvd_mul_right 8 q
  let K := cyclotomicDivisorField q (8 * q) L
  let : IsCyclotomicExtension {q} ℚ K :=
    cyclotomicDivisorField_isCyclotomicExtension q (8 * q) L hqm
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {q} ℚ K
  obtain ⟨d, aK, hd, hbound, hddiv, hdns, haK, _, hadjK, hsign⟩ :=
    exists_squarefree_generator_frobenius_sign q (8 * q) K L hqm χ hχ hprim hne
  let a : L := algebraMap K L aK
  have ha : a ^ 2 = (d : L) := by
    change (algebraMap K L aK) ^ 2 = _
    rw [← map_pow, haK, map_intCast]
  let ζ : L := zeta (8 * q) ℚ L ^ ((8 * q) / 8)
  have hζ : IsPrimitiveRoot ζ 8 :=
    (zeta_spec (8 * q) ℚ L).pow (NeZero.pos (8 * q)) (Nat.div_mul_cancel h8m).symm
  let b := ζ - ζ ^ 3
  have hb : b ^ 2 = 2 := primitive_eighth_root_difference_sq hζ
  have hadj : IntermediateField.adjoin ℚ {a} =
      characterField (8 * q) L ℂ (DirichletCharacter.changeLevel hqm χ) := by
    rw [characterField_changeLevel q K ℂ L hqm χ hχ, ← hadjK,
      IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hneq : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b} := by
    intro heq
    apply hq8
    exact primitive_level_eq_eight_of_lifted_sqrt_two_field hqm h8m χ hprim hχ b hb
      (hadj.symm.trans heq)
  refine ⟨d, a, b, hd, hbound, hddiv, hdns, ha, hb, ?_, ?_, hadj, hneq, ?_⟩
  · apply IsIntegral.of_pow (by decide : 0 < 2)
    rw [ha]
    exact isIntegral_algebraMap
  · apply IsIntegral.of_pow (by decide : 0 < 2)
    rw [hb]
    exact isIntegral_natCast 2
  · intro p hp hpn P hP σ hσ hχp
    have hc : p.Coprime (2 * q) := hp.coprime_iff_not_dvd.mpr hpn
    have h2 := (Nat.coprime_mul_iff_right.mp hc).1
    have hq := (Nat.coprime_mul_iff_right.mp hc).2
    have h8 : p.Coprime 8 := by simpa using h2.pow_right 3
    exact hsign p hp (h8.mul_right hq) P hP σ hσ hχp

end WeightedTorusJets

open scoped Pointwise

open scoped NumberField

open scoped NumberField

namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero

attribute [local instance] canonicalCyclotomicExtension

attribute [local instance] canonicalCyclotomicNumberField

attribute [local instance] canonicalCyclotomicAbelian

end WeightedTorusJets

open scoped NumberField

end SiegelZeros

end OAI
