import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import OAI.NumberTheory.SiegelZeros.Differentials.ZetaLogDerivative
import OAI.NumberTheory.SiegelZeros.EntireFunctions.GammaBound
import OAI.NumberTheory.SiegelZeros.EntireFunctions.ZeroContribution
import OAI.NumberTheory.SiegelZeros.Structure.RamifiedMass
import OAI.NumberTheory.SiegelZeros.Structure.RealBridge

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W04

theorem logarithmic_parameter_range (X : ℝ) (hX : 3 ≤ X) :
    1 < 1 + 1 / Real.log X ∧ 1 + 1 / Real.log X ≤ 2 := by
  have hXp : 0 < X := by linarith
  have hlog1 : 1 < Real.log X :=
    (Real.lt_log_iff_exp_lt hXp).2 (Real.exp_one_lt_three.trans_le hX)
  have hlog : 0 < Real.log X := by linarith
  have hinvpos : 0 < 1 / Real.log X := one_div_pos.mpr hlog
  have hinvle : 1 / Real.log X ≤ 1 :=
    (div_le_iff₀ hlog).2 (by linarith)
  constructor <;> linarith

theorem reciprocal_gap (t d : ℝ) (ht : 0 < t) (hd : 0 ≤ d) :
    1 / t - 1 / (t + d) = d / (t * (t + d)) := by
  have htd : t + d ≠ 0 := ne_of_gt (by linarith)
  field_simp [ne_of_gt ht, htd]
  ring

theorem reciprocal_gap_le (t d : ℝ) (ht : 0 < t) (hd : 0 ≤ d) :
    1 / t - 1 / (t + d) ≤ d / t ^ 2 := by
  rw [reciprocal_gap t d ht hd]
  apply div_le_div_of_nonneg_left hd (sq_pos_of_pos ht)
  nlinarith [mul_nonneg (le_of_lt ht) hd]

theorem logarithmic_reciprocal_gap_le (X β : ℝ) (hX : 1 < X) (hβ : β ≤ 1) :
    1 / ((1 + 1 / Real.log X) - 1) -
        1 / ((1 + 1 / Real.log X) - β) ≤
      (1 - β) * (Real.log X) ^ 2 := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  have h := reciprocal_gap_le (1 / Real.log X) (1 - β)
    (one_div_pos.mpr hlog) (sub_nonneg.mpr hβ)
  have heq : (1 + 1 / Real.log X) - β = 1 / Real.log X + (1 - β) := by ring
  rw [heq]
  simpa [div_pow, div_div] using h

theorem delta_substitution (q X β : ℝ) (hq : 1 < q) :
    (1 - β) * Real.log X ^ 2 =
      ((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q := by
  have hlog : Real.log q ≠ 0 := ne_of_gt (Real.log_pos hq)
  field_simp [hlog]

noncomputable def positivePrimeMass (P : Finset ℕ) (χ : ℕ → ℝ) : ℝ :=
  ∑ p ∈ P.filter (fun p => p.Prime ∧ χ p = 1), Real.log (p : ℝ) / p

theorem prime_mass_bound_from_analytic_inputs
    (P : Finset ℕ) (χ : ℕ → ℝ) (q X β C A : ℝ)
    (hq : 1 < q) (hX : 1 < X) (hβ : β ≤ 1)
    (hEuler : (2 / Real.exp 1) * positivePrimeMass P χ ≤ A)
    (hAnalytic : A ≤ C * Real.log q +
      (1 / ((1 + 1 / Real.log X) - 1) -
        1 / ((1 + 1 / Real.log X) - β))) :
    (2 / Real.exp 1) * positivePrimeMass P χ ≤
      C * Real.log q +
        ((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q := by
  have hgap := logarithmic_reciprocal_gap_le X β hX hβ
  rw [delta_substitution q X β hq] at hgap
  linarith

theorem prime_mass_unscaled_bound_from_analytic_inputs
    (P : Finset ℕ) (χ : ℕ → ℝ) (q X β C A : ℝ)
    (hq : 1 < q) (hX : 1 < X) (hβ : β ≤ 1)
    (hEuler : (2 / Real.exp 1) * positivePrimeMass P χ ≤ A)
    (hAnalytic : A ≤ C * Real.log q +
      (1 / ((1 + 1 / Real.log X) - 1) -
        1 / ((1 + 1 / Real.log X) - β))) :
    positivePrimeMass P χ ≤
      (C * Real.log q +
        ((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q) /
          (2 / Real.exp 1) := by
  apply (le_div_iff₀ (div_pos (by norm_num : (0 : ℝ) < 2)
    (Real.exp_pos 1))).2
  simpa [mul_comm] using
    prime_mass_bound_from_analytic_inputs P χ q X β C A hq hX hβ hEuler hAnalytic

end WeightedTorusJets.W04

end

section

noncomputable section
open scoped BigOperators Classical
namespace WeightedTorusJets.W63

def parity {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ :=
  if χ.Even then 0 else 1

theorem parity_cases {q : ℕ} (χ : DirichletCharacter ℂ q) :
    parity χ = 0 ∨ parity χ = 1 := by
  unfold parity
  split_ifs <;> simp

def HadamardExpansionAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (β s : ℝ) : Prop :=
  ∃ (ι : Type) (ρ : ι → ℂ),
    (∀ i, χ.LFunction (ρ i) = 0) ∧
    Summable (fun i => (((s : ℂ) - ρ i)⁻¹).re) ∧
    (∃ i, ρ i = (β : ℂ)) ∧
    (-deriv χ.LFunction (s : ℂ) / χ.LFunction (s : ℂ)).re =
      (1 / 2 : ℝ) * Real.log ((q : ℝ) / Real.pi) +
      (1 / 2 : ℝ) *
        (SiegelZerosAwei.W52.gammaLogDerivative
          (((s + (parity χ : ℝ)) / 2 : ℝ) : ℂ)).re -
      ∑' i, (((s : ℂ) - ρ i)⁻¹).re

theorem L_logDerivative_upper_of_hadamard {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hnp : χ ≠ 1) {s β : ℝ} (hs : 1 < s)
    (hhad : HadamardExpansionAt χ β s) :
    (-deriv χ.LFunction (s : ℂ) / χ.LFunction (s : ℂ)).re ≤
      (1 / 2 : ℝ) * Real.log ((q : ℝ) / Real.pi) +
      (1 / 2 : ℝ) *
        (SiegelZerosAwei.W52.gammaLogDerivative
          (((s + (parity χ : ℝ)) / 2 : ℝ) : ℂ)).re - 1 / (s - β) := by
  obtain ⟨ι, ρ, hzeros, hsum, ⟨iβ, hiβ⟩, heq⟩ := hhad
  have hz := SiegelZerosAwei.W03.retain_real_zero χ hnp ρ hzeros hs iβ hiβ hsum
  rw [heq]
  simpa only [one_div] using sub_le_sub_left hz _

theorem exists_logDerivative_upper_of_hadamard :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β s : ℝ, 1 < s → s ≤ 2 → HadamardExpansionAt χ β s →
      (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ) +
        -deriv χ.LFunction (s : ℂ) / χ.LFunction (s : ℂ)).re ≤
      C * Real.log q + (1 / (s - 1) - 1 / (s - β)) := by
  obtain ⟨CZ, hCZ, hzeta⟩ := Awei.W53.zeta_logDerivative_re_upper
  obtain ⟨CG, hCG, hgamma⟩ := SiegelZerosAwei.W52.exists_uniform_parity_gamma_bound
  refine ⟨CZ + CG + 1, by linarith, ?_⟩
  intro q _ hq χ hnp β s hs hs2 hhad
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hlog : 1 ≤ Real.log (q : ℝ) := by
    have := (Real.lt_log_iff_exp_lt hqpos).2 (Real.exp_one_lt_three.trans_le hq3)
    linarith
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
  have hconductor : Real.log ((q : ℝ) / Real.pi) ≤ Real.log q := by
    rw [Real.log_div (ne_of_gt hqpos) (ne_of_gt Real.pi_pos)]
    linarith
  have hg := hgamma s (parity χ) hs hs2 (parity_cases χ)
  have hgre : (SiegelZerosAwei.W52.gammaLogDerivative
      (((s + (parity χ : ℝ)) / 2 : ℝ) : ℂ)).re ≤ CG := by
    exact (Complex.re_le_norm _).trans hg
  have hl := L_logDerivative_upper_of_hadamard χ hnp hs hhad
  have hz := hzeta s hs hs2
  have hprod : 0 ≤ (CZ + CG) * (Real.log (q : ℝ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  simp only [Complex.add_re]
  nlinarith

theorem exists_scaled_prime_bias_of_hadamard :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ β X : ℝ, β ≤ 1 → 3 ≤ X →
      HadamardExpansionAt χ β (1 + 1 / Real.log X) →
      2 * Real.exp (-1) * SiegelZeros.W07.primeMass
        (SiegelZeros.W07.valuePrimes χ (SiegelZeros.W08.primesUpTo X) 1) ≤
      C * Real.log q + (1 - β) * Real.log X ^ 2 := by
  obtain ⟨C, hC, hupper⟩ := exists_logDerivative_upper_of_hadamard
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hnp hreal β X hβ hX hhad
  have hX1 : 1 < X := by linarith
  have hrange := W04.logarithmic_parameter_range X hX
  have hu := hupper q hq χ hnp β (1 + 1 / Real.log X) hrange.1 hrange.2 hhad
  have hl := W05.real_character_prime_mass_le_logDerivatives χ hreal hX1
    (SiegelZeros.W07.valuePrimes χ (SiegelZeros.W08.primesUpTo X) 1) (by
      intro p hp
      obtain ⟨hpS, hpχ⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hpS
      refine ⟨hprime, ?_, hpχ⟩
      exact (Nat.cast_le.mpr (Finset.mem_Ioc.mp hpI).2).trans
        (Nat.floor_le (by linarith)))
  have hgap := W04.logarithmic_reciprocal_gap_le X β hX1 hβ
  dsimp only [SiegelZeros.W07.primeMass, SiegelZeros.W07.primeWeight]
  linarith

theorem exists_prime_bias_of_hadamard :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ β X : ℝ, β ≤ 1 → 3 ≤ X →
      HadamardExpansionAt χ β (1 + 1 / Real.log X) →
      SiegelZeros.W07.primeMass
        (SiegelZeros.W07.valuePrimes χ (SiegelZeros.W08.primesUpTo X) 1) ≤
      C * Real.log q + C * (1 - β) * Real.log X ^ 2 := by
  obtain ⟨K, hK, hscaled⟩ := exists_scaled_prime_bias_of_hadamard
  have ha : 0 < 2 * Real.exp (-1) := mul_pos (by norm_num) (Real.exp_pos _)
  refine ⟨K / (2 * Real.exp (-1)), div_pos (by linarith) ha, ?_⟩
  intro q _ hq χ hnp hreal β X hβ hX hhad
  have h := hscaled q hq χ hnp hreal β X hβ hX hhad
  have herror : 0 ≤ (1 - β) * Real.log X ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hmore : (1 - β) * Real.log X ^ 2 ≤ K * ((1 - β) * Real.log X ^ 2) := by
    nlinarith
  calc
    _ ≤ (K * Real.log q + K * ((1 - β) * Real.log X ^ 2)) /
        (2 * Real.exp (-1)) := (le_div_iff₀ ha).mpr (by nlinarith)
    _ = _ := by ring

end WeightedTorusJets.W63

end

end

end SiegelZeros

end OAI
