import OAI.NumberTheory.TotientAsymptotic.Phase
import OAI.NumberTheory.TotientAsymptotic.Arithmetic

namespace OAI

/-! Normalization of totient counts and uniform coefficient asymptotics. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma g_pos (j : ℕ) : 0 < g j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [g]
    | succ n =>
      rw [g]
      apply Finset.sum_pos'
      · intro d hd
        exact (mul_pos (a_pos (by omega)) (ih (n-d) (by omega))).le
      · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
        simpa using mul_pos (a_pos (by omega)) (ih n (by omega))

lemma G_pos {x : ℝ} (hx : 0 < B x) (j : ℕ) : 0 < G x j := by
  unfold G
  apply div_pos (pow_pos hx _)
  exact mul_pos (by exact_mod_cast Nat.factorial_pos j)
    (Finset.prod_pos (fun i _ => g_pos i))

lemma scale_eventually_pos : ∀ᶠ x : ℝ in atTop,
    0 < x / Real.log x * G x (m x) := by
  have hb : Tendsto B atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ), hb.eventually (eventually_gt_atTop 0)]
    with x hx hB
  exact mul_pos (div_pos (lt_trans zero_lt_one hx) (Real.log_pos hx)) (G_pos hB _)

def normalizedCount (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  F x / (x / Real.log x * G x (m x))

/-- Ford's counting-scale bounds, with constants independent of the endpoint. -/
def FordScaleBounds : Prop :=
  ∃ cMinus cPlus : ℝ, 0 < cMinus ∧ ∀ᶠ x : ℝ in atTop,
    cMinus ≤ normalizedCount V x ∧ normalizedCount V x ≤ cPlus

/-- Exact algebra relating the normalization and the manuscript's mass error. -/
lemma normalizedCount_eq (F : ℝ → ℝ) (x : ℝ) :
    normalizedCount F x = F x * Real.log x / (x * G x (m x)) := by
  simp only [normalizedCount, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- A vanishing normalized error becomes a ratio asymptotic when the limiting
coefficient is bounded below.  No continuity of the coefficient is required. -/
theorem ratio_limit_of_normalized_error (F f : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hcoeff : ∀ s ∈ Set.Ico (0 : ℝ) 1, c ≤ A f s)
    (herr : Tendsto (fun x => normalizedCount F x - A f (theta x))
      atTop (nhds 0)) :
    Tendsto (fun x => F x / (x / Real.log x * G x (m x) * A f (theta x)))
      atTop (nhds 1) := by
  have hsmall : Tendsto
      (fun x => (normalizedCount F x - A f (theta x)) / A f (theta x))
      atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun x =>
      |normalizedCount F x - A f (theta x)| / c)
    · filter_upwards [theta_eventually_mem] with x hx
      have hA := hcoeff (theta x) hx
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (hc.trans_le hA)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hc hA
    · simpa using herr.abs.div_const c
  have hsum : Tendsto (fun x =>
      (normalizedCount F x - A f (theta x)) / A f (theta x) + 1)
      atTop (nhds 1) := by simpa using hsmall.add_const 1
  apply hsum.congr'
  filter_upwards [theta_eventually_mem, scale_eventually_pos] with x hx hscale
  have hA : A f (theta x) ≠ 0 := (hc.trans_le (hcoeff (theta x) hx)).ne'
  dsimp [normalizedCount]
  field_simp
  ring

/-- Uniform coefficient bounds and convergence from phase comparison. -/
theorem coefficient_conclusions_of_internal_comparison
    (hford : FordScaleBounds)
    (hcomp : ∀ ε : ℝ, 0 < ε → ∃ H₀ : ℕ, ∀ H ≥ H₀,
      ∀ᶠ x : ℝ in atTop,
        |normalizedCount V x - AH H (fun _ => 1) (theta x)| ≤ ε) :
    TendstoUniformlyOn (fun H => AH H (fun _ => 1)) (A (fun _ => 1))
      atTop (Set.Ico (0 : ℝ) 1) ∧
    (∃ cMinus cPlus : ℝ, 0 < cMinus ∧
      ∀ s ∈ Set.Ico (0 : ℝ) 1,
        cMinus ≤ A (fun _ => 1) s ∧ A (fun _ => 1) s ≤ cPlus) ∧
    Tendsto (fun x => V x / mainTerm x) atTop (nhds 1) := by
  obtain ⟨hunif, herr⟩ := coefficient_convergence_from_phase_comparison
    (fun _ => 1) (normalizedCount V) hcomp
  obtain ⟨cMinus, cPlus, hc, hb⟩ := hford
  have hA := coefficient_bounds_of_comparison (fun _ => 1) (normalizedCount V)
    herr cMinus cPlus hb
  exact ⟨hunif, ⟨cMinus, cPlus, hc, hA⟩,
    ratio_limit_of_normalized_error V (fun _ => 1) cMinus hc
      (fun s hs => (hA s hs).1) herr⟩

end TotientAsymptotic
end

end OAI
