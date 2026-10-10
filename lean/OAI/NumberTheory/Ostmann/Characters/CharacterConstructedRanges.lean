import OAI.NumberTheory.Ostmann.Characters.CharacterBulkSeparation

namespace OAI

/-! # The selected shells give the actual character prime ranges -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem prime_of_loglog_lower (p : ℕ) (hp : p.Prime) (a : ℝ)
    (ha : a ≤ Real.log (Real.log (p : ℝ))) : Real.exp (Real.exp a) ≤ p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h₁ := Real.exp_le_exp.mpr ha
  rw [Real.exp_log (Real.log_pos hp1)] at h₁
  have h₂ := Real.exp_le_exp.mpr h₁
  rwa [Real.exp_log hp0] at h₂

theorem prime_of_loglog_upper (p : ℕ) (hp : p.Prime) (a : ℝ)
    (ha : Real.log (Real.log (p : ℝ)) ≤ a) : (p : ℝ) ≤ Real.exp (Real.exp a) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h₁ := Real.exp_le_exp.mpr ha
  rw [Real.exp_log (Real.log_pos hp1)] at h₁
  have h₂ := Real.exp_le_exp.mpr h₁
  rwa [Real.exp_log hp0] at h₂

theorem CharacterAnchorCell.cell_loglog_bounds {P : Finset ℕ} {G : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P G c δ u) {p : ℕ} (hp : p ∈ a.cell) :
    u < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ u + 1 :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2

theorem constructed_character_anchor_ranges {P : Finset ℕ} {G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ} {u : Fin k × Bool → ℝ}
    (hP : ∀ p ∈ P, p.Prime)
    (w : ∀ j, CharacterTargetWord P G c δ U k (T j))
    (a : ∀ j, CharacterAnchorCell P G c δ (u j)) (L γs νa : ℝ)
    (hsmall : ∀ j : Fin k, u (j, false) + 1 ≤ γs * L)
    (hbig : ∀ j : Fin k, νa * L ≤ u (j, true)) :
    let R := characterPrimeCells w (characterAnchorCells a)
    (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
      (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) ∧
    (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
      Real.exp (Real.exp (νa * L)) ≤ p) := by
  intro R
  constructor
  · intro j p hp
    apply prime_of_loglog_upper p (hP p ((a (j, false)).cell_subset hp))
    exact ((a (j, false)).cell_loglog_bounds hp).2.trans (hsmall j)
  · intro j p hp
    apply prime_of_loglog_lower p (hP p ((a (j, true)).cell_subset hp))
    exact (hbig j).trans ((a (j, true)).cell_loglog_bounds hp).1.le

theorem character_top_shell_log_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : ℝ) : ∀ p ∈ loglogShell P u,
      Real.exp u ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * Real.exp u := by
  intro p hp
  have hh := Finset.mem_filter.mp hp
  have hb := prime_shell_log_bounds u p (hP p hh.1) hh.2.1 hh.2.2
  refine ⟨hb.1.le, hb.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_d9]) (Real.exp_nonneg _)

theorem eventual_character_top_dominates_bulk (z γ ν : ℝ) (hz : 0 ≤ z) (hgap : γ < ν) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℕ) (u : ℝ), (m : ℝ) ≤ z * L → ν * L ≤ u →
      (m : ℝ) * Real.exp (γ * L) ≤ Real.exp u := by
  filter_upwards [eventual_bulk_word_small (ν - γ) z (by linarith) hz] with L hL
  intro m u hm hu
  exact hL m (γ * L) u (Real.exp u) hm (by linarith) le_rfl

end Ostmann

end OAI
