import OAI.NumberTheory.Ostmann.Construction.PrimeShellIndex

namespace OAI

/-! # A rich shell supplies an actual heavy anchor cell -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem PublishedProgressionInput.rich_anchor_cell
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, u < Real.log (Real.log (p : ℝ)) ∧
        Real.log (Real.log (p : ℝ)) ≤ u + 1) →
      (∀ p ∈ P, ‖F p‖ ≤ 1) → c ≤ ∑ p ∈ P, (p : ℝ)⁻¹ →
      δ * (∑ p ∈ P, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ * (F p).re →
      ∃ h : ℕ, Real.exp u / 2 ≤ h ∧ (h : ℝ) ≤ 3 * Real.exp u ∧
        δ * c / (32 * Real.exp u) ≤ finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h ∧
        (∑ p : P, primeCellWordPrior P h p) = 1 ∧
        δ / 2 ≤ (∑ p : P, (primeCellWordPrior P h p : ℂ) * F p).re := by
  obtain ⟨C, hC, hwords⟩ := P0.rich_shell_word_priors c δ hc hδ
  have hlarge : ∀ᶠ u : ℝ in atTop, 12 ≤ Real.exp u :=
    Real.tendsto_exp_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hwords, hlarge] with u hu hu12 P F hP hshell hF hmass hbias
  let T := C * Real.exp u + 128 / (δ * c) + 1
  have hδc : 0 < δ * c := mul_pos hδ hc
  have hfrac : 0 < 64 / (δ * c) := by positivity
  have hdouble : 128 / (δ * c) = 2 * (64 / (δ * c)) := by ring
  have hT : C * Real.exp u ≤ T := by dsimp [T]; rw [hdouble]; linarith
  have hTlarge : 64 / (δ * c) < T := by
    have hCexp : 0 < C * Real.exp u := mul_pos hC (Real.exp_pos _)
    dsimp [T]
    rw [hdouble]
    linarith
  have hTpos : 0 < T := hfrac.trans hTlarge
  obtain ⟨n, w, _, hcells, herr, _⟩ := hu P F hP hshell hF hmass hbias T hT
  have hw : w ≠ [] := by
    intro he
    rw [he, List.sum_nil, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_pos hTpos] at herr
    linarith
  obtain ⟨h, hh⟩ := List.exists_mem_of_ne_nil w hw
  obtain ⟨hm, hprob, hmean⟩ := hcells h hh
  have hmpos : 0 < finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h :=
    (by positivity : 0 < δ * c / (32 * Real.exp u)).trans_le hm
  have hfiber : (P.filter (fun p => primeLogIndex p = h)).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp [finiteCellMass, he] at hmpos
  obtain ⟨p, hp⟩ := hfiber
  obtain ⟨hpP, hph⟩ := Finset.mem_filter.mp hp
  have hind := prime_shell_index_bounds u hu12 p (hP p hpP) (hshell p hpP).1 (hshell p hpP).2
  rw [hph] at hind
  have hscale := shell_floor_scale u (by linarith)
  exact ⟨h, hscale.1.trans hind.1, hind.2.trans (by nlinarith [hscale.2]), hm, hprob, hmean⟩

end Ostmann

end OAI
