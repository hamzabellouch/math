import OAI.NumberTheory.Ostmann.Construction.PrimeShellIndex
import OAI.NumberTheory.Ostmann.Construction.TargetShellLocation
import OAI.NumberTheory.Ostmann.Construction.RichGridShell

namespace OAI

/-! # Actual prime-cell words for every pivot and filler target -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def loglogShell (P : Finset ℕ) (u : ℝ) : Finset ℕ :=
  P.filter (fun p => u < Real.log (Real.log (p : ℝ)) ∧
    Real.log (Real.log (p : ℝ)) ≤ u + 1)

theorem loglogShell_mass (P : Finset ℕ) (u : ℝ) :
    (∑ p ∈ loglogShell P u, (p : ℝ)⁻¹) =
      weightedIntervalMass P (fun p => Real.log (Real.log (p : ℝ)))
        (fun p => (p : ℝ)⁻¹) u (u + 1) := rfl

/-- A target window contains a whole rich tested shell. Its good cell word
has bounded length, positive means, and bounded target error. All constants
are independent of the late block's location. -/
theorem PublishedProgressionInput.target_prime_word
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (k : ℕ), 20000 ≤ k → C ≤ Real.exp ((k : ℝ) / 10000) →
      ∀ (τ : ℝ), 0 < τ → U ≤ Real.log τ →
      Real.log τ ≤ U + 2 * (k : ℝ) / 10000 →
      ∀ (P : Finset ℕ) (F : ℕ → ℂ), (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ‖F p‖ ≤ 1) →
      (∀ u v : ℝ, U ≤ u → v ≤ U + 5 * k → (k : ℝ) / 10000 ≤ v - u →
        ∃ j : ℕ, u ≤ U + j ∧ U + j + 1 ≤ v ∧
          c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) →
      (∀ j : ℕ, j ≤ 5 * k → c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (F p).re) →
      ∀ T : ℝ, (2 : ℝ) ^ (k - 1) * τ / 4 ≤ T → T ≤ 600 * (4 : ℝ) ^ k * τ →
      ∃ (j n : ℕ) (w : List ℕ),
        j ≤ 5 * k ∧ c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ ∧
        Real.log T - 2 * (k : ℝ) / 10000 ≤ U + j ∧
        U + j + 1 ≤ Real.log T - (k : ℝ) / 10000 ∧
        w.length = n ∧
        (∀ h ∈ w,
          δ * c / (32 * Real.exp (U + j)) ≤
            finiteCellMass (loglogShell P (U + j)) primeLogIndex (fun p => (p : ℝ)⁻¹) h ∧
          (∑ p : loglogShell P (U + j), primeCellWordPrior _ h p) = 1 ∧
          δ / 2 ≤ (∑ p : loglogShell P (U + j),
            (primeCellWordPrior _ h p : ℂ) * F p).re) ∧
        |(w.sum : ℝ) - T| < 64 / (δ * c) ∧
        (n : ℝ) ≤ 256 / (δ * c) * Real.exp (2 * (k : ℝ) / 10000) := by
  obtain ⟨C, hC, hwords⟩ := P0.rich_shell_word_priors c δ hc hδ
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hwords
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop U₀] with U hU k hk hCk τ hτ hτlo hτhi P F hP hF hrich htest T hTlo hThi
  have hT : 0 < T := (by positivity : 0 < (2 : ℝ) ^ (k - 1) * τ / 4).trans_le hTlo
  obtain ⟨hwlo, hwhi⟩ := target_window_in_late_block k hk U τ T hτ hτlo hτhi hTlo hThi
  obtain ⟨j, hjlo, hjhi, hjmass⟩ := hrich
    (Real.log T - 2 * (k : ℝ) / 10000) (Real.log T - (k : ℝ) / 10000)
    hwlo hwhi (by linarith)
  have hloc : U₀ ≤ U + j := hU.trans (le_add_of_nonneg_right (Nat.cast_nonneg j))
  have hs := target_shell_scale (1 / 10000) k T (U + j) hT
    (by convert hjlo using 1; ring) (by convert hjhi using 1; ring)
  have hslo : Real.exp ((k : ℝ) / 10000) * Real.exp (U + j) ≤ T := by
    simpa only [show (1 / 10000 : ℝ) * k = (k : ℝ) / 10000 by ring] using hs.1
  have hshi : T ≤ Real.exp (2 * (k : ℝ) / 10000) * Real.exp (U + j) := by
    simpa only [show 2 * (1 / 10000 : ℝ) * k = 2 * (k : ℝ) / 10000 by ring] using hs.2
  have hsmall : ∀ p ∈ loglogShell P (U + j),
      Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4 := by
    intro p hp
    obtain ⟨hpP, hpL, hpU⟩ := Finset.mem_filter.mp hp
    have hupper : Real.log (p : ℝ) ≤ T * Real.exp (-(k : ℝ) / 10000) := by
      have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (hP p hpP).one_lt)
      have he := Real.exp_le_exp.mpr (hpU.trans hjhi)
      rw [Real.exp_log hlogp, Real.exp_sub, Real.exp_log hT] at he
      rw [show -(k : ℝ) / 10000 = -((k : ℝ) / 10000) by ring, Real.exp_neg]
      simpa only [div_eq_mul_inv] using he
    exact hupper.trans (target_window_below_cutoff k hk τ T hτ hThi).le
  have hjbound : j ≤ 5 * k := by
    have hcast : (j : ℝ) ≤ 5 * k := by linarith
    exact_mod_cast hcast
  obtain ⟨n, w, hlen, hcells, herr, hn⟩ := hU₀ (U + j) hloc (loglogShell P (U + j)) F
    (fun p hp => hP p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => hF p (Finset.mem_filter.mp hp).1) hjmass (htest j hjbound hjmass hsmall) T
    ((mul_le_mul_of_nonneg_right hCk (Real.exp_pos _).le).trans hslo)
  refine ⟨j, n, w, hjbound, hjmass, hjlo, hjhi, hlen, hcells, herr, ?_⟩
  have hcost : 0 ≤ 256 / (δ * c) := by positivity
  have hbound := hn.trans (mul_le_mul_of_nonneg_left hshi hcost)
  exact (mul_le_mul_iff_left₀ (Real.exp_pos (U + j))).mp (by
    simpa only [mul_assoc] using hbound)

end Ostmann

end OAI
