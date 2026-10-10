import OAI.NumberTheory.TotientAsymptotic.ComparisonLargePart

namespace OAI

/-! Ford's cutoff restrictions in the normalized coordinates of the finite grid. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def comparisonCutoffs (y : ℝ) (ν : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.exp (Real.exp (B y*ν j))

lemma comparisonCutoffs_doubleLog {y : ℝ} (hB : B y ≠ 0) (ν : ℕ → ℝ) (j : ℕ) :
    B (comparisonCutoffs y ν j)/B y=ν j := by
  simp only [comparisonCutoffs,B,Real.log_exp]
  exact mul_div_cancel_left₀ _ hB

lemma comparison_upper_cutoff_power : ∀ᶠ y : ℝ in atTop,
    Real.exp (Real.exp ((4/5 : ℝ)*B y)) ≤ y^(1/(10*B y)) := by
  filter_upwards [comparison_small_part_cost,eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with y hcost hy hB
  have he : Real.exp ((4/5 : ℝ)*B y) ≤ Real.log y/(10*B y) := by
    apply (le_div_iff₀ (by positivity : 0 < 10*B y)).mpr
    nlinarith [Real.exp_pos ((4/5 : ℝ)*B y)]
  apply (Real.log_le_log_iff (Real.exp_pos _) (Real.rpow_pos_of_pos (zero_lt_one.trans hy) _)).mp
  rw [Real.log_exp,Real.log_rpow (zero_lt_one.trans hy)]
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using he

/-- A finite grid with these normalized inequalities satisfies exactly the
published Ford parameter restrictions, including the first-cutoff power. -/
theorem ford_parameters_of_normalized_grid : ∀ᶠ y : ℝ in atTop,
    ∀ b D r : ℕ, ∀ S : ℝ, ∀ ν μ : ℕ → ℝ,
    1 ≤ b → ν 0=1 → Real.exp (Real.exp 1) ≤ S → S ≤ comparisonCutoffs y ν b →
    (∀ j ∈ Finset.range b, ν (j+1) < μ j ∧ μ j < ν j) → ν 1 ≤ 4/5 →
    (∀ j ∈ Finset.Icc 2 b,
      2*Real.sqrt (B S/B y) < ν (j-1)-ν j) →
    1 ≤ D → (D : ℝ) ≤ y^(1/100 : ℝ) →
    (largestPrimeFactor D : ℝ) ≤ comparisonCutoffs y ν b →
    1 ≤ r → (r : ℝ) ≤ y^(1/10 : ℝ) →
    FordComparisonParameters b y S D r (comparisonCutoffs y ν) (comparisonCutoffs y μ) := by
  filter_upwards [comparison_upper_cutoff_power,eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with y hpower hy hB
  intro b D r S ν μ hb hν hS hSb horder hν1 hgap hD hDy hDs hr hry
  refine ⟨hb,?_,hS,hSb,?_,?_,?_,hD,hDy,hDs,hr,hry⟩
  · simp only [comparisonCutoffs,hν,mul_one,B,
      Real.exp_log (Real.log_pos hy),Real.exp_log (zero_lt_one.trans hy)]
  · intro j hj
    exact ⟨Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left (horder j hj).1 hB)),
      Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left (horder j hj).2 hB))⟩
  · apply le_trans _ hpower
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left hν1 hB.le).trans_eq (mul_comm _ _)
  · intro j hj
    simpa only [comparisonCutoffs_doubleLog hB.ne'] using hgap j hj

end TotientAsymptotic

end

end OAI
