import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace OAI

namespace SiegelZeros


namespace W56

theorem character_nat_eq_of_prime_eq {q m : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ m)
    (hq : q ≠ 1) (hm : m ≠ 1)
    (hprime : ∀ p : ℕ, p.Prime → p.Coprime (q * m) →
      χ (p : ZMod q) = ψ (p : ZMod m))
    (n : ℕ) (hn : n.Coprime (q * m)) : χ (n : ZMod q) = ψ (n : ZMod m) := by
  revert hn
  induction n using Nat.recOnMul with
  | zero =>
    intro hn
    simp [DirichletCharacter.map_zero' χ hq, DirichletCharacter.map_zero' ψ hm]
  | one => intro hn; simp
  | prime p hp => intro hn; exact hprime p hp hn
  | mul a b ha hb =>
    intro hn
    have hc := Nat.coprime_mul_iff_left.mp hn
    simpa only [Nat.cast_mul, map_mul] using congrArg₂ (· * ·) (ha hc.1) (hb hc.2)

theorem changeLevel_eq_of_prime_eq {q m : ℕ} [NeZero q] [NeZero m]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ m)
    (hq : q ≠ 1) (hm : m ≠ 1)
    (hprime : ∀ p : ℕ, p.Prime → p.Coprime (q * m) →
      χ (p : ZMod q) = ψ (p : ZMod m)) :
    χ.changeLevel (Nat.dvd_mul_right q m) = ψ.changeLevel (Nat.dvd_mul_left m q) := by
  apply MulChar.ext
  intro u
  let n := (u : ZMod (q * m)).val
  have hncast : (n : ZMod (q * m)) = (u : ZMod (q * m)) := ZMod.natCast_zmod_val _
  have hn : n.Coprime (q * m) :=
    (ZMod.isUnit_iff_coprime n (q * m)).mp (by rw [hncast]; exact u.isUnit)
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd, ← hncast]
  simp only [ZMod.cast_natCast (Nat.dvd_mul_right q m),
    ZMod.cast_natCast (Nat.dvd_mul_left m q)]
  exact character_nat_eq_of_prime_eq χ ψ hq hm hprime n hn

theorem primitive_levels_eq_of_changeLevel_eq {q m : ℕ} [NeZero q] [NeZero m]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ m)
    (hq : χ.IsPrimitive) (hm : ψ.IsPrimitive)
    (heq : χ.changeLevel (Nat.dvd_mul_right q m) =
      ψ.changeLevel (Nat.dvd_mul_left m q)) : q = m := by
  have hfg := DirichletCharacter.factorsThrough_gcd χ ψ heq
  have hqg : q ∣ Nat.gcd q m := by
    have h := DirichletCharacter.conductor_dvd_of_mem_conductorSet χ hfg
    rwa [hq] at h
  have hfg' : ψ.FactorsThrough (Nat.gcd q m) := by
    refine ⟨Nat.gcd_dvd_right q m, hfg.χ₀, ?_⟩
    apply DirichletCharacter.changeLevel_injective (Nat.dvd_mul_left m q)
    calc
      ψ.changeLevel (Nat.dvd_mul_left m q) =
          χ.changeLevel (Nat.dvd_mul_right q m) := heq.symm
      _ = (hfg.χ₀.changeLevel (Nat.gcd_dvd_left q m)).changeLevel
          (Nat.dvd_mul_right q m) :=
        congrArg (DirichletCharacter.changeLevel (Nat.dvd_mul_right q m))
          hfg.eq_changeLevel
      _ = (hfg.χ₀.changeLevel (Nat.gcd_dvd_right q m)).changeLevel
          (Nat.dvd_mul_left m q) := by
        rw [← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]
  have hmg : m ∣ Nat.gcd q m := by
    have h := DirichletCharacter.conductor_dvd_of_mem_conductorSet ψ hfg'
    rwa [hm] at h
  exact Nat.dvd_antisymm (hqg.trans (Nat.gcd_dvd_right q m))
    (hmg.trans (Nat.gcd_dvd_left q m))

def chiEightComplex : DirichletCharacter ℂ 8 :=
  ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

@[simp] theorem chiEightComplex_apply (x : ZMod 8) :
    chiEightComplex x = (ZMod.χ₈ x : ℂ) := rfl

private theorem chiEightComplex_not_factorsThrough (d : ℕ)
    (hfive : (5 : ZMod d) = 1) : ¬ chiEightComplex.FactorsThrough d := by
  rintro ⟨hd, ψ, hψ⟩
  have hv := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hd
    (ZMod.unitOfCoprime 5 (by decide : Nat.Coprime 5 8))
  rw [← hψ] at hv
  simp only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd] at hv
  norm_num only [Nat.cast_ofNat] at hv
  rw [hfive, map_one, chiEightComplex_apply] at hv
  norm_num [ZMod.χ₈] at hv

theorem chiEightComplex_isPrimitive : chiEightComplex.IsPrimitive := by
  have hd := DirichletCharacter.conductor_dvd_level chiEightComplex
  have hf := DirichletCharacter.factorsThrough_conductor chiEightComplex
  have hle := Nat.le_of_dvd (by decide : 0 < 8) hd
  change chiEightComplex.conductor = 8
  generalize chiEightComplex.conductor = d at *
  interval_cases d <;> norm_num at hd
  all_goals try rfl
  · exact False.elim (chiEightComplex_not_factorsThrough 1 (by decide) hf)
  · exact False.elim (chiEightComplex_not_factorsThrough 2 (by decide) hf)
  · exact False.elim (chiEightComplex_not_factorsThrough 4 (by decide) hf)

theorem conductor_eight_of_prime_values {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : q ≠ 1) (hp : χ.IsPrimitive)
    (hprime : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ q →
      χ (p : ZMod q) = (ZMod.χ₈ (p : ZMod 8) : ℂ)) : q = 8 := by
  apply primitive_levels_eq_of_changeLevel_eq χ chiEightComplex hp chiEightComplex_isPrimitive
  apply changeLevel_eq_of_prime_eq χ chiEightComplex hq (by decide)
  intro p hpp hcop
  have hnot : ¬ p ∣ q * 8 := hpp.coprime_iff_not_dvd.mp hcop
  have hp2 : p ≠ 2 := by
    intro h
    apply hnot
    subst p
    exact dvd_mul_of_dvd_right (by decide : 2 ∣ 8) q
  have hpq : ¬ p ∣ q := fun h => hnot (dvd_mul_of_dvd_left h 8)
  exact hprime p hpp hp2 hpq

end W56


end SiegelZeros

end OAI
