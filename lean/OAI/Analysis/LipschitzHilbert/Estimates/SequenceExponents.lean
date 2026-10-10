import OAI.Analysis.LipschitzHilbert.Phase.FourthMoment
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! The finite-dimensional exponent comparison used in the Fourier gain. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

/-- Raising the finite mean inequality gives the exact fourth-moment cost
of changing the coefficient exponent from `4/3` to `r`. -/
theorem fourth_power_exponent_comparison (a : ι → ℂ) {r : ℝ}
    (hr : 4 / 3 ≤ r) :
    (∑ i, coefficientMass a i) ^ 3 ≤
      (Fintype.card ι : ℝ) ^ (3 - 4 / r) * (∑ i, ‖a i‖ ^ r) ^ (4 / r) := by
  have hr0 : 0 < r := by linarith
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (Finset.univ : Finset ι) (f := coefficientMass a)
    (p := 3 * r / 4) (by linarith) (fun i _ => coefficientMass_nonneg a i)
  have hinner (i : ι) : coefficientMass a i ^ (3 * r / 4) = ‖a i‖ ^ r := by
    rw [coefficientMass, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  simp only [Finset.card_univ, hinner] at h
  have hpow := Real.rpow_le_rpow
    (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => coefficientMass_nonneg a i)) _) h
    (show 0 ≤ 4 / r by positivity)
  rw [← Real.rpow_mul (Finset.sum_nonneg (fun i _ => coefficientMass_nonneg a i)),
    Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)),
    ← Real.rpow_mul (Nat.cast_nonneg _)] at hpow
  have hleft : (3 * r / 4) * (4 / r) = 3 := by field_simp
  have hright : (3 * r / 4 - 1) * (4 / r) = 3 - 4 / r := by field_simp
  simpa only [hleft, hright, Real.rpow_ofNat] using hpow

theorem fourth_power_exponent_comparison_bound (a : ι → ℂ) {r D : ℝ}
    (hr : 4 / 3 ≤ r) (hD : (Fintype.card ι : ℝ) ≤ D) :
    (∑ i, coefficientMass a i) ^ 3 ≤
      D ^ (3 - 4 / r) * (∑ i, ‖a i‖ ^ r) ^ (4 / r) := by
  apply (fourth_power_exponent_comparison a hr).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)) _)
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) hD
  have hr0 : 0 < r := by linarith
  rw [sub_nonneg, div_le_iff₀ hr0]
  linarith

omit [Fintype ι] in
theorem dimension_cost_le_exp {D c : ℝ} (hD : 1 ≤ D) (hc : 0 ≤ c) :
    D ^ (c / Real.log (2 * D)) ≤ Real.exp c := by
  have hD0 : 0 < D := by linarith
  have hlog : 0 < Real.log (2 * D) := Real.log_pos (by linarith)
  have hlogs : Real.log D ≤ Real.log (2 * D) :=
    Real.log_le_log hD0 (by linarith)
  rw [Real.rpow_def_of_pos hD0]
  apply Real.exp_le_exp.mpr
  rw [← mul_div_assoc, div_le_iff₀ hlog]
  nlinarith [mul_le_mul_of_nonneg_left hlogs hc]

omit [Fintype ι] in
theorem fourth_exponent_parameters {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1 / 3) :
    4 / 3 ≤ 4 / (3 - θ) ∧ 4 / (3 - θ) ≤ 3 / 2 ∧
      3 - 4 / (4 / (3 - θ)) = θ := by
  have hd : 0 < 3 - θ := by linarith
  refine ⟨(le_div_iff₀ hd).2 (by linarith),
    (div_le_iff₀ hd).2 (by linarith), ?_⟩
  field_simp
  ring

theorem fourth_power_exponent_comparison_exp (a : ι → ℂ) {D c θ : ℝ}
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) (hc : 0 ≤ c)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1 / 3) (hdef : θ = c / Real.log (2 * D)) :
    (∑ i, coefficientMass a i) ^ 3 ≤
      Real.exp c * (∑ i, ‖a i‖ ^ (4 / (3 - θ))) ^ (3 - θ) := by
  obtain ⟨hr, _, heq⟩ := fourth_exponent_parameters hθ hθ'
  have h := fourth_power_exponent_comparison_bound a hr hcard
  have hinv : 4 / (4 / (3 - θ)) = 3 - θ := by linarith [heq]
  rw [hinv, sub_sub_cancel] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)) _))
  rw [hdef]
  exact dimension_cost_le_exp hD hc

/-- The manuscript's absolute phase constant `2⁻⁶⁰`. -/
def phaseConstant : ℝ := 1 / 1152921504606846976

/-- The manuscript's threshold `2⁻¹⁰` for a dominant coefficient. -/
def atomThreshold : ℝ := 1 / 1024

omit [Fintype ι] in
theorem phaseConstant_pos : 0 < phaseConstant := by norm_num [phaseConstant]

omit [Fintype ι] in
theorem atomThreshold_range : 0 < atomThreshold ∧ atomThreshold < 1 := by
  norm_num [atomThreshold]

omit [Fintype ι] in
theorem phaseConstant_le_gap : phaseConstant ≤ atomThreshold ^ 4 / 16384 := by
  norm_num [phaseConstant, atomThreshold]

omit [Fintype ι] in
theorem phaseParameter_range {D : ℝ} (hD : 1 ≤ D) :
    0 < phaseConstant / Real.log (2 * D) ∧
      phaseConstant / Real.log (2 * D) ≤ 1 / 3 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 * D) := by
    have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    exact htwo.trans (Real.log_le_log (by norm_num) (by linarith))
  have hpos : 0 < Real.log (2 * D) := by linarith
  refine ⟨div_pos phaseConstant_pos hpos, (div_le_iff₀ hpos).2 ?_⟩
  have hc : phaseConstant ≤ (1 / 6 : ℝ) := by norm_num [phaseConstant]
  linarith

omit [Fintype ι] in
theorem deficit_absorbs_exponential {δ c : ℝ} (hcδ : c ≤ δ) :
    (1 - δ) * Real.exp c ≤ 1 := by
  calc
    (1 - δ) * Real.exp c ≤ Real.exp (-δ) * Real.exp c := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos c).le
      linarith [Real.add_one_le_exp (-δ)]
    _ = Real.exp (c - δ) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)

omit [Fintype ι] in
theorem phaseConstant_exp_le_two : Real.exp phaseConstant ≤ 2 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hc : phaseConstant ≤ Real.log 2 := by
    have : phaseConstant ≤ (1 / 2 : ℝ) := by norm_num [phaseConstant]
    linarith
  calc
    Real.exp phaseConstant ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hc
    _ = 2 := Real.exp_log (by norm_num)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
