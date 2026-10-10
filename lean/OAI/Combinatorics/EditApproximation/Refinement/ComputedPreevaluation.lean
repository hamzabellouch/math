import OAI.Combinatorics.EditApproximation.Refinement.PhysicalInputGuard
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter

private theorem guard_scalar (H : ℕ) (hH : 1000000 ≤ H) :
    100000 * (H + 1005) ^ 2 ≤ H ^ 4 := by
  have hplus : H + 1005 ≤ 2 * H := by omega
  have hp := Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left hplus 2)
  have hcoef : 400000 ≤ H ^ 2 := by nlinarith only [hH]
  have hm := Nat.mul_le_mul_right (H ^ 2) hcoef
  calc
    _ ≤ 100000 * (2 * H) ^ 2 := hp
    _ = 400000 * H ^ 2 := by ring
    _ ≤ H ^ 2 * H ^ 2 := hm
    _ = _ := by ring

 theorem physicalLargeInputWithWork_le_height (N : ℕ) (epsilon : BinaryFraction)
    (hH : 1000000 ≤ inputHeight N)
    (hmass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N) :
    (physicalLargeInputWithWork N epsilon).2 ≤ inputHeight N ^ 4 :=
  (physicalLargeInputWithWork_cost N epsilon hmass).trans (guard_scalar _ hH)

/-- All input scans, index construction, parameter arithmetic and the
bounded accuracy/word-cap decision occur before sampling. -/


private theorem setup_scalar (N H a b c : ℕ) (hH : 1000000 ≤ H)
    (ha : a ≤ (N + 2) * H ^ 4) (hb : b ≤ 2000 * (H + 1)) (hc : c ≤ H ^ 4) :
    a + b + c ≤ (N + 2) * H ^ 5 := by
  have hb' : 2000 * (H + 1) ≤ H ^ 2 := by nlinarith only [hH]
  have hs : H ^ 2 ≤ H ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hcoef0 := Nat.mul_le_mul_left (N + 2) (show 2 ≤ H by omega)
  have hcoef : N + 2 + 2 ≤ (N + 2) * H := by omega
  calc
    _ ≤ (N + 2) * H ^ 4 + H ^ 4 + H ^ 4 := by omega
    _ = (N + 2 + 2) * H ^ 4 := by ring
    _ ≤ ((N + 2) * H) * H ^ 4 := Nat.mul_le_mul_right _ hcoef
    _ = _ := by ring

 theorem integerPreevaluationWork_near_linear (C : ℕ) (epsilonTime : ℝ) (htime : 0 < epsilonTime) :
    ∀ᶠ N in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      ∀ epsilon : BinaryFraction,
      (integerPreevaluationWork source target N epsilon : ℝ) ≤
        (N + 2 : ℝ) ^ (1 + epsilonTime) := by
  filter_upwards [fixed_height_power_near_linear 5 epsilonTime htime,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop (max 1000000 C)),
    computed_localOnlineMassBound_word] with N ht hH hmass
  intro source target hsize halphabet epsilon
  have hheight : 1000000 ≤ inputHeight N :=
    (le_max_left _ _).trans (hH.trans (computed_smallLog_le_height N))
  have hC : C ≤ inputHeight N :=
    (le_max_right _ _).trans (hH.trans (computed_smallLog_le_height N))
  have hp := integerPreprocessingWork_le source target N C hsize halphabet (by omega) hC
  have hg := globalParameterWork_le N
  have hd := physicalLargeInputWithWork_le_height N epsilon hheight hmass
  have hbound := setup_scalar N (inputHeight N) _ _ _ hheight hp hg hd
  exact (show (integerPreevaluationWork source target N epsilon : ℝ) ≤
      (N + 2 : ℝ) * (inputHeight N : ℝ) ^ 5 by exact_mod_cast hbound).trans ht

end EditApproximation

end OAI
