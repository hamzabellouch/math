import Mathlib.Analysis.Complex.ExponentialBounds
import OAI.NumberTheory.Ostmann.Construction.PrimeCellWordPriors
import OAI.NumberTheory.Ostmann.Arithmetic.WeightedIntervalMass

namespace OAI

/-! # Whole unit shells fit the integer cell scale

Taking the floor of the lower exponential endpoint retains every prime in
the shell, including its two boundary cells.
-/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem prime_shell_log_bounds (u : ℝ) (p : ℕ) (hp : p.Prime)
    (hlo : u < Real.log (Real.log (p : ℝ)))
    (hhi : Real.log (Real.log (p : ℝ)) ≤ u + 1) :
    Real.exp u < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ Real.exp 1 * Real.exp u := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  constructor
  · simpa only [Real.exp_log hlog] using Real.exp_lt_exp.mpr hlo
  · have h := Real.exp_le_exp.mpr hhi
    simpa only [Real.exp_log hlog, Real.exp_add, mul_comm] using h

theorem prime_shell_index_bounds (u : ℝ) (hu : 12 ≤ Real.exp u)
    (p : ℕ) (hp : p.Prime)
    (hlo : u < Real.log (Real.log (p : ℝ)))
    (hhi : Real.log (Real.log (p : ℝ)) ≤ u + 1) :
    (⌊Real.exp u⌋₊ : ℝ) ≤ primeLogIndex p ∧
      (primeLogIndex p : ℝ) ≤ 3 * ⌊Real.exp u⌋₊ := by
  obtain ⟨hl, hh⟩ := prime_shell_log_bounds u p hp hlo hhi
  have hf := Nat.floor_le (Real.exp_pos u).le
  have hceil : ⌊Real.exp u⌋₊ < ⌈Real.log (p : ℝ)⌉₊ :=
    Nat.lt_ceil.mpr (hf.trans_lt hl)
  have hlow : ⌊Real.exp u⌋₊ ≤ primeLogIndex p := by
    unfold primeLogIndex
    omega
  have hfloor : (12 : ℝ) ≤ ⌊Real.exp u⌋₊ := by
    exact_mod_cast (Nat.le_floor hu : 12 ≤ ⌊Real.exp u⌋₊)
  have hnext := Nat.lt_floor_add_one (Real.exp u)
  have he : Real.exp 1 ≤ (11 : ℝ) / 4 := by linarith [Real.exp_one_lt_d9]
  have hupper := mul_le_mul_of_nonneg_right he (Real.exp_pos u).le
  have hind := (primeLogIndex_bounds p hp).1
  constructor
  · exact_mod_cast hlow
  · nlinarith

theorem shell_floor_scale (u : ℝ) (hu : 2 ≤ Real.exp u) :
    Real.exp u / 2 ≤ (⌊Real.exp u⌋₊ : ℝ) ∧
      (⌊Real.exp u⌋₊ : ℝ) ≤ Real.exp u := by
  have hlo : (1 : ℝ) ≤ ⌊Real.exp u⌋₊ := by
    have hone : (1 : ℝ) ≤ Real.exp u := by linarith
    exact_mod_cast (Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ Real.exp u from by simpa only [Nat.cast_one] using hone) :
      1 ≤ ⌊Real.exp u⌋₊)
  have hi := Nat.lt_floor_add_one (Real.exp u)
  exact ⟨by linarith, Nat.floor_le (Real.exp_pos u).le⟩

theorem PublishedProgressionInput.rich_shell_word_priors
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ u : ℝ in atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, u < Real.log (Real.log (p : ℝ)) ∧
        Real.log (Real.log (p : ℝ)) ≤ u + 1) →
      (∀ p ∈ P, ‖F p‖ ≤ 1) → c ≤ ∑ p ∈ P, (p : ℝ)⁻¹ →
      δ * (∑ p ∈ P, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ * (F p).re →
      ∀ T : ℝ, C * Real.exp u ≤ T → ∃ (n : ℕ) (w : List ℕ),
        w.length = n ∧
        (∀ h ∈ w,
          δ * c / (32 * Real.exp u) ≤ finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h ∧
          (∑ p : P, primeCellWordPrior P h p) = 1 ∧
          δ / 2 ≤ (∑ p : P, (primeCellWordPrior P h p : ℂ) * F p).re) ∧
        |(w.sum : ℝ) - T| < 64 / (δ * c) ∧
        (n : ℝ) * Real.exp u ≤ 256 / (δ * c) * T := by
  obtain ⟨C, hC, hwords⟩ := P0.rich_prime_word_priors c δ hc hδ
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp hwords
  refine ⟨C, hC, ?_⟩
  have hlarge : ∀ᶠ u : ℝ in atTop, max 12 (B₀ + 1) ≤ Real.exp u :=
    Real.tendsto_exp_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with u hu P F hP hshell hF hmass hbias T hT
  have hu12 : 12 ≤ Real.exp u := (le_max_left _ _).trans hu
  have hscale := shell_floor_scale u (by linarith)
  have hB₀' : B₀ ≤ (⌊Real.exp u⌋₊ : ℝ) := by
    have h := (le_max_right 12 (B₀ + 1)).trans hu
    have h' := Nat.lt_floor_add_one (Real.exp u)
    linarith
  have hCT : C * (⌊Real.exp u⌋₊ : ℝ) ≤ T :=
    (mul_le_mul_of_nonneg_left hscale.2 hC.le).trans hT
  obtain ⟨n, w, hw, hcells, herr, hn⟩ := hB₀ _ hB₀' P F hP
    (fun p hp => prime_shell_index_bounds u hu12 p (hP p hp) (hshell p hp).1 (hshell p hp).2)
    hF hmass hbias T hCT
  refine ⟨n, w, hw, ?_, herr, ?_⟩
  · intro h hh
    obtain ⟨hm, hprob, hb⟩ := hcells h hh
    refine ⟨?_, hprob, hb⟩
    apply le_trans _ hm
    exact div_le_div_of_nonneg_left (mul_nonneg hδ.le hc.le)
      (by nlinarith [Real.exp_pos u]) (by nlinarith [hscale.2])
  · have h := mul_le_mul_of_nonneg_left hscale.1 (Nat.cast_nonneg n)
    calc
      (n : ℝ) * Real.exp u = 2 * ((n : ℝ) * (Real.exp u / 2)) := by ring
      _ ≤ 2 * ((n : ℝ) * (⌊Real.exp u⌋₊ : ℝ)) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ 2 * (128 / (δ * c) * T) := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = _ := by ring

end Ostmann

end OAI
