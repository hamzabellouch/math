import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace SourcePrimeFactor
open OrdinaryCorrelations Finset Filter

def characterModulation (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (n : ℕ) : ℂ := f n * star (χ (n : ZMod q))

lemma characterModulation_bound {f : ℕ → ℂ} (hf : OneBounded f)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : OneBounded (characterModulation f χ) := by
  intro n
  simp only [characterModulation, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (χ.norm_le_one _)

lemma characterModulation_multiplicative {f : ℕ → ℂ} (hm : Multiplicative f)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : Multiplicative (characterModulation f χ) := by
  intro m n hm0 hn0 hmn
  simp only [characterModulation, hm m n hm0 hn0 hmn, Nat.cast_mul, map_mul, star_mul]
  ring

def jointCharacter {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q*r) :=
  χ.changeLevel (Nat.dvd_mul_right q r) * ψ.changeLevel (Nat.dvd_mul_left r q)

lemma changeLevel_nat {q m : ℕ} (χ : DirichletCharacter ℂ q) (hqm : q ∣ m)
    {n : ℕ} (hn : n.Coprime m) : χ.changeLevel hqm (n : ZMod m) = χ (n : ZMod q) := by
  have hh := χ.changeLevel_eq_cast_of_dvd hqm (ZMod.unitOfCoprime n hn)
  simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hqm] using hh

lemma character_nonunit_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : ¬n.Coprime q) : χ (n : ZMod q) = 0 := by
  exact χ.map_nonunit (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h))

lemma jointCharacter_apply {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) (n : ℕ) :
    jointCharacter χ ψ (n : ZMod (q*r)) = χ (n : ZMod q) * ψ (n : ZMod r) := by
  by_cases hn : n.Coprime (q*r)
  · simp only [jointCharacter, MulChar.mul_apply, changeLevel_nat _ _ hn]
  · rw [character_nonunit_zero (jointCharacter χ ψ) hn]
    obtain hq | hr := not_and_or.mp (fun h => hn (Nat.coprime_mul_iff_right.mpr h))
    · rw [character_nonunit_zero χ hq, zero_mul]
    · rw [character_nonunit_zero ψ hr, mul_zero]

lemma characterModulation_distance_joint (f : ℕ → ℂ) {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (t X : ℝ) :
    distanceSq (characterModulation f χ) ψ t X = distanceSq f (jointCharacter χ ψ) t X := by
  unfold distanceSq
  apply sum_congr rfl
  intro p hp
  rw [jointCharacter_apply]
  simp only [characterModulation, star_mul, mul_assoc, mul_comm, mul_left_comm]

theorem characterModulation_nonpretentious {f : ℕ → ℂ}
    (hNP : UniformlyNonpretentious f) {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) : UniformlyNonpretentious (characterModulation f χ) := by
  intro r hr ψ
  have hh := hNP (q*r) (Nat.mul_pos hq hr) (jointCharacter χ ψ)
  simpa only [distance, characterModulation_distance_joint] using hh

end SourcePrimeFactor

end

end OAI
