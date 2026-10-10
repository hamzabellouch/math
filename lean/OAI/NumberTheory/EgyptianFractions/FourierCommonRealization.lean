import OAI.NumberTheory.EgyptianFractions.LevelFailureMean

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.FourierCommonRealization

/-- The random-product second moment hypotheses imply one common collection
    of 1000 sample blocks, simultaneously good at all middle and terminal scales.
    This is stated directly in normalized Fourier averages. -/
theorem exists_common_fourier_realization :
    ∃ N : ℕ, ∀ (Ω J : Type) [Fintype Ω] [Nonempty Ω]
      (tests : Finset J) (level : J → Finset ℕ) (X : J → ℝ) (m : ℝ)
      (freq : Finset ℕ) (terminalFreq : ℕ → Finset ℕ)
      (phase : Ω → ℕ → ℕ → ℂ) (w : ℕ → ℝ) (terminal : Finset ℕ),
      500000 ≤ m → (tests.card : ℝ) ≤ m →
      (∀ j ∈ tests, 0 < X j) →
      (∀ j ∈ tests, ((level j).card : ℝ) ≤ X j) →
      ((freq.card : ℝ) ≤ Real.exp (4 * m / 10000)) →
      (∀ j ∈ tests, ∀ u ∈ level j, (9999 / 10000 : ℝ) * m ≤ w u) →
      (∀ j ∈ tests, ∀ u ∈ level j, ∀ l ∈ freq,
        (∑ ω, ‖phase ω u l‖ ^ 2) / Fintype.card Ω ≤ Real.exp (-w u / 100)) →
      (∀ u ∈ terminal, N ≤ u) →
      (∀ u ∈ terminal, ((terminalFreq u).card : ℝ) ≤
        Real.exp (4 * Real.log (u : ℝ) / 10000)) →
      (∀ u ∈ terminal, ∀ l ∈ terminalFreq u,
        (∑ ω, ‖phase ω u l‖ ^ 2) / Fintype.card Ω ≤
          Real.exp (-Real.log (u : ℝ) / 100)) →
      ∃ f : Fin 1000 → Ω,
        (∀ j ∈ tests,
          (((level j).filter (fun u => ∃ l ∈ freq,
            Real.exp (-3 * m / 10000) < ‖phase (f 0) u l‖)).card : ℝ) ≤
              X j * Real.exp (-m / 1000)) ∧
        ∀ u ∈ terminal, ∃ i : Fin 1000, ∀ l ∈ terminalFreq u,
          ‖phase (f i) u l‖ ≤ Real.exp (-3 * Real.log (u : ℝ) / 10000) := by
  classical
  obtain ⟨N, hN⟩ := LevelFailureMean.exists_good_levels_and_terminal_blocks
  refine ⟨max N 1, ?_⟩
  intro Ω J _ _ tests level X m freq terminalFreq phase w terminal
    hm htests hX hlevels hfreq hw hmoment hterminal htfreq htmoment
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  let middleBad : Ω → ℕ → Prop := fun ω u =>
    ∃ l ∈ freq, Real.exp (-3 * m / 10000) < ‖phase ω u l‖
  let terminalBad : Ω → ℕ → Prop := fun ω u =>
    ∃ l ∈ terminalFreq u,
      Real.exp (-3 * Real.log (u : ℝ) / 10000) < ‖phase ω u l‖
  have hmiddle : ∀ j ∈ tests, ∀ u ∈ level j,
      ((Finset.univ.filter (fun ω => middleBad ω u)).card : ℝ) /
        Fintype.card Ω ≤ Real.exp (-m / 200) := by
    intro j hj u hu
    apply FourierFailureBounds.middle_failure_fraction_le
      freq (fun ω l => phase ω u l) m (w u) (by linarith) (hw j hj u hu) hfreq
    intro l hl
    have h := (div_le_iff₀ hΩ).mp (hmoment j hj u hu l hl)
    simpa only [mul_comm] using h
  have htcut : ∀ u ∈ terminal, N ≤ u := by
    intro u hu
    exact (le_max_left N 1).trans (hterminal u hu)
  have hbad : ∀ u ∈ terminal,
      ((Finset.univ.filter (fun ω => terminalBad ω u)).card : ℝ) /
        Fintype.card Ω ≤ (u : ℝ) ^ (-(1 / 200 : ℝ)) := by
    intro u hu
    have hu1 : 1 ≤ u := (le_max_right N 1).trans (hterminal u hu)
    apply FourierFailureBounds.terminal_failure_fraction_le
      (terminalFreq u) (fun ω l => phase ω u l) (u : ℝ)
      (by exact_mod_cast hu1) (htfreq u hu)
    intro l hl
    have h := (div_le_iff₀ hΩ).mp (htmoment u hu l hl)
    simpa only [mul_comm] using h
  obtain ⟨f, hf, ht⟩ := hN Ω J tests level X m middleBad terminalBad terminal
    hm htests hX hlevels hmiddle htcut hbad
  refine ⟨f, hf, ?_⟩
  intro u hu
  obtain ⟨i, hi⟩ := ht u hu
  refine ⟨i, ?_⟩
  intro l hl
  exact le_of_not_gt (fun h => hi ⟨l, hl, h⟩)

end Problem337.FourierCommonRealization

end

end OAI
