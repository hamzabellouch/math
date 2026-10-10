import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! # The finite algebra of subexponential losses -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- A lower bound of the form `exp (-o(r))`, expressed without a choice
of error function. -/
def HasSubexponentialLowerBound (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop, Real.exp (-ε * r) ≤ f r

/-- An upper bound of the form `exp (o(r))`. -/
def HasSubexponentialUpperBound (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop, f r ≤ Real.exp (ε * r)

theorem HasSubexponentialLowerBound.eventually_pos {f : ℝ → ℝ}
    (hf : HasSubexponentialLowerBound f) : ∀ᶠ r in atTop, 0 < f r :=
  (hf 1 zero_lt_one).mono (fun _ hr => (Real.exp_pos _).trans_le hr)

theorem HasSubexponentialLowerBound.mono {f g : ℝ → ℝ}
    (hf : HasSubexponentialLowerBound f) (hfg : f ≤ᶠ[atTop] g) :
    HasSubexponentialLowerBound g := by
  intro ε hε
  filter_upwards [hf ε hε, hfg] with r hr hfg'
  exact hr.trans hfg'

theorem HasSubexponentialUpperBound.mono {f g : ℝ → ℝ}
    (hg : HasSubexponentialUpperBound g) (hfg : f ≤ᶠ[atTop] g) :
    HasSubexponentialUpperBound f := by
  intro ε hε
  filter_upwards [hg ε hε, hfg] with r hr hfg'
  exact hfg'.trans hr

theorem subexponential_lower_const {c : ℝ} (hc : 0 < c) :
    HasSubexponentialLowerBound (fun _ => c) := by
  intro ε hε
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hε)
  have he := ht.eventually (gt_mem_nhds hc)
  simpa only [Function.comp_def, id_eq, neg_mul] using he.mono (fun _ h => h.le)

theorem subexponential_upper_const (c : ℝ) :
    HasSubexponentialUpperBound (fun _ => c) := by
  intro ε hε
  exact (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hε)).eventually
    (eventually_ge_atTop c)

theorem HasSubexponentialLowerBound.mul {f g : ℝ → ℝ}
    (hf : HasSubexponentialLowerBound f) (hg : HasSubexponentialLowerBound g) :
    HasSubexponentialLowerBound (fun r => f r * g r) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by positivity), hg (ε / 2) (by positivity)] with r hr hs
  calc
    Real.exp (-ε * r) = Real.exp (-(ε / 2) * r) * Real.exp (-(ε / 2) * r) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ f r * g r := mul_le_mul hr hs (Real.exp_pos _).le ((Real.exp_pos _).trans_le hr).le

theorem HasSubexponentialUpperBound.mul {f g : ℝ → ℝ}
    (hf : HasSubexponentialUpperBound f) (hg : HasSubexponentialUpperBound g)
    (hf0 : ∀ᶠ r in atTop, 0 ≤ f r) :
    HasSubexponentialUpperBound (fun r => f r * g r) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by positivity), hg (ε / 2) (by positivity), hf0] with r hr hs h0
  calc
    f r * g r ≤ f r * Real.exp (ε / 2 * r) := mul_le_mul_of_nonneg_left hs h0
    _ ≤ Real.exp (ε / 2 * r) * Real.exp (ε / 2 * r) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ = Real.exp (ε * r) := by rw [← Real.exp_add]; congr 1; ring

theorem HasSubexponentialLowerBound.div {f g : ℝ → ℝ}
    (hf : HasSubexponentialLowerBound f) (hg : HasSubexponentialUpperBound g)
    (hg0 : ∀ᶠ r in atTop, 0 < g r) :
    HasSubexponentialLowerBound (fun r => f r / g r) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by positivity), hg (ε / 2) (by positivity), hg0] with r hr hs h0
  calc
    Real.exp (-ε * r) = Real.exp (-(ε / 2) * r) / Real.exp (ε / 2 * r) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    _ ≤ f r / g r := div_le_div₀ ((Real.exp_pos _).trans_le hr).le hr h0 hs

end PolycyclicRecognition

end OAI
