import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasBandSelectionBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Characters Ostmann.Preliminaries Filter
open scoped BigOperators

def quadraticBiasValue (d : Decomposition) (p : ℕ) : ℝ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    (maxTranslatedBias (d.residueSupport p) (quadraticCharacter p) : ℝ)
  else 0

lemma quadraticBiasValue_prime (d : Decomposition) (p : ℕ) [Fact p.Prime] :
    quadraticBiasValue d p =
      (maxTranslatedBias (d.residueSupport p) (quadraticCharacter p) : ℝ) := by
  simp [quadraticBiasValue, Fact.out]

lemma quadraticBiasValue_nonneg (d : Decomposition) (p : ℕ) :
    0 ≤ quadraticBiasValue d p := by
  unfold quadraticBiasValue
  split_ifs <;> positivity

lemma maxTranslatedBias_quadratic_le_one {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) : (maxTranslatedBias S (quadraticCharacter p) : ℝ) ≤ 1 := by
  classical
  obtain ⟨t, ht⟩ := exists_max_quadratic_translation S
  rw [ht, quadraticResidueMean, abs_div, abs_of_nonneg (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)]
  by_cases hS : S.Nonempty
  · apply (div_le_iff₀ (by exact_mod_cast hS.card_pos : (0 : ℝ) < S.card)).mpr
    calc
      |∑ x ∈ S, quadraticReal p (x-t)| ≤ ∑ x ∈ S, |quadraticReal p (x-t)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun x hx => abs_quadraticReal_le_one _)
      _ = 1*S.card := by simp
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

lemma quadraticBiasValue_le_one (d : Decomposition) (p : ℕ) :
    quadraticBiasValue d p ≤ 1 := by
  unfold quadraticBiasValue
  split_ifs with hp
  · let : Fact p.Prime := ⟨hp⟩
    exact maxTranslatedBias_quadratic_le_one _
  · norm_num

def closedLogarithmicPrimeBand (T : ℝ) : Finset ℕ := by
  classical
  exact (⌊Real.exp (2*T)⌋₊).primesLE.filter (fun p => T ≤ Real.log p)

@[simp] lemma mem_closedLogarithmicPrimeBand {T : ℝ} {p : ℕ} :
    p ∈ closedLogarithmicPrimeBand T ↔ p.Prime ∧ T ≤ Real.log p ∧ Real.log p ≤ 2*T := by
  classical
  simp only [closedLogarithmicPrimeBand, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpu, hp⟩, hlo⟩
    refine ⟨hp,hlo,(Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mpr ?_⟩
    exact (by exact_mod_cast hpu : (p : ℝ) ≤ ⌊Real.exp (2*T)⌋₊).trans
      (Nat.floor_le (Real.exp_pos _).le)
  · rintro ⟨hp,hlo,hhi⟩
    exact ⟨⟨Nat.le_floor ((Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mp hhi),hp⟩,hlo⟩

lemma boundedClosedLogarithmicPrimeBand_image (Q : ℕ) (T : ℝ)
    (hQ : ⌊Real.exp (2*T)⌋₊ ≤ Q) :
    (boundedClosedLogarithmicPrimeBand Q T).image Subtype.val = closedLogarithmicPrimeBand T := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact mem_closedLogarithmicPrimeBand.mpr
      ⟨primeUpTo_prime q,(mem_boundedClosedLogarithmicPrimeBand.mp hq)⟩
  · intro hp
    have hh := mem_closedLogarithmicPrimeBand.mp hp
    have hu : p ≤ ⌊Real.exp (2*T)⌋₊ :=
      Nat.le_floor ((Real.log_le_iff_le_exp (by exact_mod_cast hh.1.pos)).mp hh.2.2)
    refine Finset.mem_image.mpr ⟨⟨p,Nat.mem_primesLE.mpr ⟨hu.trans hQ,hh.1⟩⟩,?_,rfl⟩
    exact mem_boundedClosedLogarithmicPrimeBand.mpr hh.2

end Ostmann.QuadraticCenter

end

end OAI
