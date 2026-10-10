import OAI.Probability.SATComputability.EffectiveTrialValues
import OAI.Probability.SATComputability.UpperCertificates

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec PeriodicLattice.CertifiedReal
open scoped NNReal

local instance compiledTrialsRatPrimcodable : Primcodable ℚ :=
  PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def decodeTrial (j : ℕ) : TrialData :=
  (Encodable.decode j).getD (0,0,.zero,[])

@[fun_prop] theorem decodeTrial_computable : Computable decodeTrial := by
  unfold decodeTrial
  fun_prop

theorem decodeTrial_encode (t : TrialData) : decodeTrial (Encodable.encode t) = t := by
  simp [decodeTrial]

noncomputable def trialDataValid (t : TrialData) : Bool :=
  decide (0 < t.1 ∧ 0 < t.2.1) && exponentCheck t.2.2.2

@[fun_prop] theorem trialDataValid_computable : Computable trialDataValid := by
  unfold trialDataValid
  fun_prop

theorem trialDataValid_iff (t : TrialData) : trialDataValid t = true ↔
    0 < t.1 ∧ 0 < t.2.1 ∧ exponentCheck t.2.2.2 = true := by
  simp only [trialDataValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

private noncomputable def trialApproximation : TrialData × ℕ → ℚ :=
  Classical.choose trialValue_effective

private theorem trialApproximation_computable : Computable trialApproximation :=
  (Classical.choose_spec trialValue_effective).1

private theorem trialApproximation_error (t : TrialData) (s : ℕ) :
    |trialValue t - (trialApproximation (t,s) : ℝ)| ≤ error s :=
  (Classical.choose_spec trialValue_effective).2 t s

noncomputable def satTrialEvaluation : TrialEvaluation where
  density j := (decodeTrial j).1
  valid j := trialDataValid (decodeTrial j)
  value j := trialValue (decodeTrial j)
  approximate p := trialApproximation (decodeTrial p.1, 2^p.2)
  density_computable := by fun_prop
  valid_computable := by fun_prop
  approximate_computable := trialApproximation_computable.comp (by fun_prop)
  density_positive j hj := ((trialDataValid_iff _).mp hj).1
  approximation_error j s _ := by
    rw [abs_sub_comm]
    apply (trialApproximation_error _ _).trans
    simp only [error, tolerance, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat]
    rw [one_div]
    apply inv_anti₀ (by positivity)
    push_cast
    exact le_add_of_nonneg_right (by norm_num)

theorem satTrialEvaluation_valid {j : ℕ} (hj : satTrialEvaluation.valid j = true) :
    0 < (decodeTrial j).1 ∧ 0 < (decodeTrial j).2.1 ∧
      exponentCheck (decodeTrial j).2.2.2 = true :=
  (trialDataValid_iff _).mp hj

theorem satTrialEvaluation_penalty {j : ℕ} (hj : satTrialEvaluation.valid j = true) :
    0 < (decodeTrial j).2.1 := (satTrialEvaluation_valid hj).2.1

theorem satTrialEvaluation_bound {j : ℕ} (hj : satTrialEvaluation.valid j = true) :
    satPressure (trialDensityNN (decodeTrial j)) ((decodeTrial j).2.1 : ℝ) ≤
      satTrialEvaluation.value j := by
  have ht := satTrialEvaluation_valid hj
  change _ ≤ trialValue (decodeTrial j)
  rw [trialValue_eq_functional _ ht.2.2]
  apply satPressure_le_rational_trial
  · change (0 : ℝ) < (max 0 (decodeTrial j).1 : ℚ)
    exact_mod_cast lt_max_of_lt_right ht.1
  · exact_mod_cast ht.2.1
  · exact (exponentCheck_iff _).mp ht.2.2

end FixedClauseThreshold.Computability

end OAI
