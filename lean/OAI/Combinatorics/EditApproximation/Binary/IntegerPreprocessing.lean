import OAI.Combinatorics.EditApproximation.Binary.IntegerInputInspection
import OAI.Combinatorics.EditApproximation.Refinement.ComputedWidthEnvelope
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter
open scoped Topology



 theorem integerEqualWithWork_spec (source target : List ℤ) :
    (integerEqualWithWork source target).1 = decide (source = target) ∧
      (integerEqualWithWork source target).2 ≤ source.length + target.length + 1 := by
  induction source generalizing target with
  | nil => cases target <;> simp [integerEqualWithWork]
  | cons x xs ih =>
    cases target with
    | nil => simp [integerEqualWithWork]
    | cons y ys =>
      by_cases hxy : x = y
      · subst y
        have h := ih ys
        constructor
        · simpa [integerEqualWithWork] using h.1
        · simpa [integerEqualWithWork, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (show (integerEqualWithWork xs ys).2 + 1 ≤ xs.length + ys.length + 3 by omega)
      · simp [integerEqualWithWork, hxy]

/-- Scans, integer encoding, indexed occurrence preprocessing and the
exact equality guard are charged before the local evaluator starts. -/


 theorem input_length_bits_le (N : ℕ) : Nat.size (N + 2) ≤ inputHeight N + 1 := by
  apply Nat.size_le.mpr
  exact (inputHeight_covers_length N).trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _))

private theorem preprocessing_scalar_bound (N H C L s p : ℕ)
    (hH : 8 ≤ H) (hC : C ≤ H) (hL : L ≤ H + 1)
    (hs : s ≤ C * L + 3) (hp : p ≤ L) :
    4 * N + 2 * s + 2 * p + 8 + 3 * N + N * ((3 * C + 2) * L + 14) + (N + 1) + 1 ≤
      (N + 2) * H ^ 4 := by
  have hCL := Nat.mul_le_mul hC hL
  have hs' : s ≤ 3 * H ^ 2 := by nlinarith only [hs, hCL, hH]
  have hp' : p ≤ H + 1 := hp.trans hL
  have hcoef0 := Nat.mul_le_mul (by omega : 3 * C + 2 ≤ 3 * H + 2) hL
  have hcoef : (3 * C + 2) * L + 22 ≤ 10 * H ^ 2 := by
    nlinarith only [hcoef0, hH]
  have hcN := Nat.mul_le_mul_left N hcoef
  have hsquare : 10 * H ^ 2 ≤ H ^ 4 := by
    have hh : 10 ≤ H ^ 2 := by nlinarith only [hH]
    have hm := Nat.mul_le_mul_right (H ^ 2) hh
    nlinarith only [hm]
  have hm := Nat.mul_le_mul_left (N + 2) hsquare
  nlinarith only [hs', hp', hcN, hm, hH]

 theorem integerPreprocessingWork_le (source target : List ℤ) (N C : ℕ)
    (hsize : source.length + target.length ≤ N)
    (halphabet : ∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C)
    (hH : 8 ≤ inputHeight N) (hC : C ≤ inputHeight N) :
    integerPreprocessingWork source target ≤ (N + 2) * inputHeight N ^ 4 := by
  have hi := integerInputInspectionWithWork_cost source target
  have heq := (integerEqualWithWork_spec source target).2
  have hoc := integerOccurrenceBuildWithWork_polynomial source target N C hsize halphabet
  have hs := integerInputSymbolBits_polynomial source target N C halphabet
  have hp : integerInputPositionBits target ≤ Nat.size (N + 2) := Nat.size_le_size (by omega)
  have hscalar := preprocessing_scalar_bound N (inputHeight N) C (Nat.size (N + 2))
    (integerInputSymbolBits source target) (integerInputPositionBits target) hH hC
    (input_length_bits_le N) hs hp
  unfold integerPreprocessingWork
  rw [encodeIntegerSymbolsWithWork_spec, encodeIntegerSymbolsWithWork_spec]
  dsimp only
  omega

 theorem fixed_height_power_near_linear (C : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, (N + 2 : ℝ) * (inputHeight N : ℝ) ^ C ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hlimit := hlog.const_mul (C : ℝ)
  simp only [mul_zero] at hlimit
  have hf : Tendsto (fun N => ((C : ℝ) * Real.log (inputHeight N : ℝ)) / inputHeight N)
      atTop (𝓝 0) := by convert hlimit using 1; ext N; ring
  filter_upwards [sublinear_height_near_linear _ hf epsilon hepsilon] with N hN
  rwa [← nat_pow_eq_exp_log (inputHeight N) C (Nat.two_pow_pos _)] at hN

 theorem integerPreprocessingWork_near_linear (C : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      (integerPreprocessingWork source target : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [fixed_height_power_near_linear 4 epsilon hepsilon,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop (max 8 C))] with N htime hH
  intro source target hsize halphabet
  have hn := integerPreprocessingWork_le source target N C hsize halphabet
    ((le_max_left _ _).trans (hH.trans (computed_smallLog_le_height N)))
    ((le_max_right _ _).trans (hH.trans (computed_smallLog_le_height N)))
  exact (show (integerPreprocessingWork source target : ℝ) ≤
    (N + 2 : ℝ) * (inputHeight N : ℝ) ^ 4 by exact_mod_cast hn).trans htime

end EditApproximation

end OAI
