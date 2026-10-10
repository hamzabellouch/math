import OAI.NumberTheory.EgyptianFractions.TerminalAssembly
import OAI.NumberTheory.EgyptianFractions.TerminalBridge

namespace OAI
noncomputable section

namespace Problem337.TerminalAssembly

/-- The fixed coefficient in the constructive terminal length estimate. -/
def terminalCoefficient (D α : ℝ) : ℝ :=
  D / Real.log 2 + 1 / (-Real.log α) + 3

theorem terminalCoefficient_pos {D α : ℝ}
    (hD : 1 ≤ D) (hα : 0 < α) (hα1 : α < 1) :
    0 < terminalCoefficient D α := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogα : 0 < -Real.log α := neg_pos.2 (Real.log_neg hα hα1)
  have hD0 : 0 < D := by linarith
  unfold terminalCoefficient
  positivity

/-- Rounding the terminal budget costs at most one extra logarithmic unit. -/
theorem ceiling_length_add_depth {B K S : ℝ} {d : ℕ}
    (hB : 0 ≤ B) (hlog : 1 ≤ Real.log S)
    (hd : (d : ℝ) ≤ K * Real.log S) :
    ((⌈B * Real.log S⌉₊ + d : ℕ) : ℝ) ≤ (B + K + 1) * Real.log S := by
  have hceil : (⌈B * Real.log S⌉₊ : ℝ) < B * Real.log S + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hB (by linarith))
  push_cast
  nlinarith

/-- Direct finite-tuple terminal data for a real cutoff.  The residue hypothesis
is the genuine arithmetic input; no intermediate expansions are assumed. -/
theorem terminal_finite_expansions
    (M : ℕ) (X D α S : ℝ) (hX : 0 ≤ X)
    (hXM : X < (M : ℝ)) (hXS : X ≤ Real.exp S)
    (hD : 1 ≤ D) (hα : 0 < α) (hα1 : α < 1)
    (hS : 1 ≤ S) (hlogS : 1 ≤ Real.log S)
    (hdiv : 2 ^ TerminalDepth.binaryExponent D S ∣ M)
    (hstep : ∀ u : ℕ, (u : ℝ) ≤ X → S ^ D < (u : ℝ) →
      ∃ t z h : ℕ, 0 < t ∧ 0 < z ∧ t ∣ M ∧
        (h : ℝ) ≤ (u : ℝ) ^ α ∧ t + h = u * z) :
    ∀ u ∈ Finset.Icc 1 ⌊X⌋₊,
      Descent.UnitListAtMost ((u : ℚ) / M)
        ⌈terminalCoefficient D α * Real.log S⌉₊ := by
  have hUM : ⌊X⌋₊ < M := by
    exact_mod_cast (Nat.floor_le hX).trans_lt hXM
  have hUS : (⌊X⌋₊ : ℝ) ≤ Real.exp S := (Nat.floor_le hX).trans hXS
  have hstep' : ∀ u : ℕ, u ≤ ⌊X⌋₊ → S ^ D < (u : ℝ) →
      ∃ t z h : ℕ, 0 < t ∧ 0 < z ∧ t ∣ M ∧
        (h : ℝ) ≤ (u : ℝ) ^ α ∧ t + h = u * z := by
    intro u hu
    exact hstep u ((Nat.cast_le.mpr hu).trans (Nat.floor_le hX))
  intro u hu
  obtain ⟨l, hl, hsum, hlen⟩ := terminal_expansion_of_residue_supply M ⌊X⌋₊ D α S
    hUM hD hα hα1 hS hlogS hUS hdiv hstep' u (Finset.mem_Icc.mp hu).2
  apply Descent.UnitListAtMost.of_list_real l hlen
  · intro n hn
    have := hl n hn
    omega
  · exact hsum

/-- The terminal tuple budget together with all backward levels remains
logarithmic, with one explicit coefficient independent of the cutoff. -/
theorem terminal_finite_total_budget {D α K S : ℝ} {d : ℕ}
    (hD : 1 ≤ D) (hα : 0 < α) (hα1 : α < 1)
    (hlogS : 1 ≤ Real.log S) (hd : (d : ℝ) ≤ K * Real.log S) :
    ((⌈terminalCoefficient D α * Real.log S⌉₊ + d : ℕ) : ℝ) ≤
      (terminalCoefficient D α + K + 1) * Real.log S :=
  ceiling_length_add_depth (terminalCoefficient_pos hD hα hα1).le hlogS hd

end Problem337.TerminalAssembly

end

end OAI
