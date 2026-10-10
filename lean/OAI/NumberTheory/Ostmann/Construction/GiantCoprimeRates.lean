import OAI.NumberTheory.Ostmann.Construction.GiantCoprimeIntervals
import OAI.NumberTheory.Ostmann.Arithmetic.RootCellErrorRates

namespace OAI

/-! # The top-giant coprimality loss is below the joint comparison error -/

namespace Ostmann
open Filter
open scoped Classical

theorem giant_coprime_error_rate (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ u K : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u →
      K ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      Real.exp 2 * (K * Real.exp (-u)) ≤ Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [weighted_giant_atom_rate C d,
    constant_mul_double_exp_le (Real.exp 2) 1 (13 / 1000) (125 / 10000)
      (Real.exp_pos _).le (by norm_num) (by norm_num) (by norm_num)] with L hL hconst
  intro u K hu hK
  exact (mul_le_mul_of_nonneg_left (hL u K hu hK) (Real.exp_pos _).le).trans
    (by simpa only [one_mul, neg_mul] using hconst)

theorem prime_pair_coprime_removal_rate (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ u v r s K : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → s ≤ r + 1 → 0 ≤ K →
      K ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ∀ F : ℕ → ℕ → ℂ,
      (∀ p ∈ giantPrimes u v, ∀ q ∈ giantPrimes r s, ‖F p q‖ ≤ K) →
      ‖complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
        if (⌊Real.exp x⌋₊).Coprime ⌊Real.exp y⌋₊ then F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ else 0)) -
        complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
          F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊))‖ ≤ Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [giant_coprime_error_rate C d] with L hL
  intro u v r s K hu hs hK hbudget F hF
  refine (prime_pair_coprime_removal u v r s F K hK hF).trans (le_trans ?_ (hL u K hu hbudget))
  have hm : reciprocalPrimeInterval 1 0 (Real.exp r) (Real.exp s) ≤ Real.exp 2 :=
    (reciprocalPrimeInterval_le_exp 1 0 r s).trans (Real.exp_le_exp.mpr (by linarith))
  calc
    _ ≤ K * Real.exp (-u) * Real.exp 2 := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := mul_comm _ _

theorem mixed_pair_coprime_removal_rate (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ u v r s J K : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → v ≤ J + 1 → s ≤ r + 1 → 0 ≤ K →
      K ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ∀ F : ℕ → ℕ → ℂ,
      (∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, ∀ q ∈ giantPrimes r s, ‖F p q‖ ≤ K) →
      ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
        if (⌊Real.exp x⌋₊).Coprime ⌊Real.exp y⌋₊ then F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ else 0)) -
        complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
          F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊))‖ ≤ Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [giant_coprime_error_rate C d] with L hL
  intro u v r s J K hr hv hs hK hbudget F hF
  refine (mixed_pair_coprime_removal u v r s J F K hK hF).trans (le_trans ?_ (hL r K hr hbudget))
  have hm : reciprocalPrimeInterval 1 0 (Real.exp r) (Real.exp s) ≤ Real.exp (s - r) :=
    reciprocalPrimeInterval_le_exp 1 0 r s
  have he : Real.exp (v - J) * Real.exp (s - r) ≤ Real.exp 2 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ K * Real.exp (v - J) * Real.exp (-r) * Real.exp (s - r) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (K * Real.exp (-r)) * (Real.exp (v - J) * Real.exp (s - r)) := by ring
    _ ≤ (K * Real.exp (-r)) * Real.exp 2 := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := mul_comm _ _

end Ostmann

end OAI
