import OAI.NumberTheory.Ostmann.Construction.SmoothMeanDecayRates

namespace OAI

/-! # The integral conductor cutoff in (5.14) -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def sparseTruncationDegree (C L : ℝ) : ℕ := ⌈C * L⌉₊

noncomputable def sparseConductorCutoff (C L : ℝ) : ℕ :=
  ⌈Real.exp (2 * (sparseTruncationDegree C L : ℝ) * Real.exp ((9 / 10 : ℝ) * L))⌉₊

theorem sparseConductorCutoff_pos (C L : ℝ) : 0 < sparseConductorCutoff C L :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

theorem sparseConductorCutoff_log_lower (C L : ℝ) :
    2 * (sparseTruncationDegree C L : ℝ) * Real.exp ((9 / 10 : ℝ) * L) ≤
      Real.log (sparseConductorCutoff C L) := by
  have hh := Nat.le_ceil (Real.exp
    (2 * (sparseTruncationDegree C L : ℝ) * Real.exp ((9 / 10 : ℝ) * L)))
  have hp := Real.log_le_log (Real.exp_pos _) hh
  simpa only [Real.log_exp, sparseConductorCutoff] using hp

theorem sparseConductorCutoff_log_upper (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L) :
    Real.log (sparseConductorCutoff C L) ≤ (2 * C + 3) * L * Real.exp ((9 / 10 : ℝ) * L) := by
  let S := 2 * (sparseTruncationDegree C L : ℝ) * Real.exp ((9 / 10 : ℝ) * L)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have he : 1 ≤ Real.exp S := Real.one_le_exp hS
  have hc := Nat.ceil_lt_add_one (Real.exp_nonneg S)
  have hc' : (sparseConductorCutoff C L : ℝ) ≤ 2 * Real.exp S := by
    dsimp [sparseConductorCutoff]
    change (⌈Real.exp S⌉₊ : ℝ) ≤ _
    linarith
  have hp : 0 < (sparseConductorCutoff C L : ℝ) := by
    exact_mod_cast sparseConductorCutoff_pos C L
  have hlog := Real.log_le_log hp hc'
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hk : (sparseTruncationDegree C L : ℝ) ≤ C * L + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hC (by linarith))).le
  have hEL : 1 ≤ Real.exp ((9 / 10 : ℝ) * L) := Real.one_le_exp (by positivity)
  have h2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  dsimp [S] at hlog
  have hmul := mul_le_mul_of_nonneg_right hk (Real.exp_nonneg ((9 / 10 : ℝ) * L))
  nlinarith

theorem eventual_sparseConductorCutoff (C : ℝ) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, 101 ≤ sparseConductorCutoff C L ∧
      L ^ 2 ≤ Real.log (sparseConductorCutoff C L) ∧
      Real.log (sparseConductorCutoff C L) ≤
        (2 * C + 3) * L * Real.exp ((9 / 10 : ℝ) * L) := by
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop 1
    (show (0 : ℝ) < 9 / 10 by norm_num))).bound (show 0 < 2 * C by positivity)
  filter_upwards [hsmall, eventually_ge_atTop (11 : ℝ)] with L hs hL
  have hL0 : 0 ≤ L := by linarith
  have hs' : L ≤ 2 * C * Real.exp ((9 / 10 : ℝ) * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg hL0,
      abs_of_pos (Real.exp_pos _)] using hs
  have hk : C * L ≤ (sparseTruncationDegree C L : ℝ) := Nat.le_ceil _
  have hlower : L ^ 2 ≤ Real.log (sparseConductorCutoff C L) := by
    have hmul := mul_le_mul_of_nonneg_right hs' hL0
    have hmul' := mul_le_mul_of_nonneg_right hk (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    have hh := sparseConductorCutoff_log_lower C L
    nlinarith
  have hpos : 0 < (sparseConductorCutoff C L : ℝ) := by
    exact_mod_cast sparseConductorCutoff_pos C L
  have hnum : (101 : ℝ) ≤ sparseConductorCutoff C L := by
    have hh := Real.log_le_self hpos.le
    nlinarith
  exact ⟨by exact_mod_cast hnum, hlower, sparseConductorCutoff_log_upper C L hC.le (by linarith)⟩

theorem sparse_product_le_conductor_cutoff {ι : Type*} (S : Finset ι) (p : ι → ℕ)
    (C L : ℝ) (hp : ∀ i ∈ S, 0 < p i)
    (hlog : ∀ i ∈ S, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L))
    (hcard : S.card ≤ 2 * sparseTruncationDegree C L) :
    ∏ i ∈ S, p i ≤ sparseConductorCutoff C L := by
  have hprod : (0 : ℝ) < ∏ i ∈ S, (p i : ℝ) :=
    Finset.prod_pos (fun i hi => by exact_mod_cast hp i hi)
  have hsum : (∑ i ∈ S, Real.log (p i)) ≤
      2 * (sparseTruncationDegree C L : ℝ) * Real.exp ((9 / 10 : ℝ) * L) := by
    calc
      _ ≤ ∑ _i ∈ S, Real.exp ((9 / 10 : ℝ) * L) := Finset.sum_le_sum hlog
      _ = (S.card : ℝ) * Real.exp ((9 / 10 : ℝ) * L) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.exp_nonneg _)
  have he : (∏ i ∈ S, (p i : ℝ)) ≤ Real.exp
      (2 * (sparseTruncationDegree C L : ℝ) * Real.exp ((9 / 10 : ℝ) * L)) := by
    apply (Real.log_le_iff_le_exp hprod).mp
    rw [Real.log_prod (fun i hi => (by exact_mod_cast (hp i hi).ne' : (p i : ℝ) ≠ 0))]
    exact hsum
  have hh : (∏ i ∈ S, (p i : ℝ)) ≤ (sparseConductorCutoff C L : ℝ) :=
    he.trans (Nat.le_ceil _)
  exact_mod_cast hh

end Ostmann

end OAI
