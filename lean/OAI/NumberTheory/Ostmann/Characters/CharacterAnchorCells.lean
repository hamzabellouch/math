import OAI.NumberTheory.Ostmann.Construction.RichAnchorCell
import OAI.NumberTheory.Ostmann.Characters.CharacterMeanRotation

namespace OAI

/-! # Actual small and large anchor cells with their original harmonic laws -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

structure CharacterAnchorCell (P : Finset ℕ) (F : ℕ → ℂ) (c δ u : ℝ) where
  index : ℕ
  lower : Real.exp u / 2 ≤ index
  upper : (index : ℝ) ≤ 3 * Real.exp u
  mass : δ * c / (32 * Real.exp u) ≤
    ∑ p ∈ (loglogShell P u).filter (fun p => primeLogIndex p = index), (p : ℝ)⁻¹
  mean : δ / 2 ≤ (∑ p : P,
    (primeSubsetPrior P ((loglogShell P u).filter
      (fun p => primeLogIndex p = index)) p : ℂ) * F p).re

noncomputable def CharacterAnchorCell.cell {P : Finset ℕ} {F : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) : Finset ℕ :=
  (loglogShell P u).filter (fun p => primeLogIndex p = a.index)

theorem CharacterAnchorCell.cell_subset {P : Finset ℕ} {F : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) : a.cell ⊆ P :=
  (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

theorem CharacterAnchorCell.cell_eq_of_index {P : Finset ℕ} {F G : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) (b : CharacterAnchorCell P G c δ u)
    (h : a.index = b.index) : a.cell = b.cell := by
  simp only [CharacterAnchorCell.cell, h]

theorem CharacterAnchorCell.cell_mass_pos {P : Finset ℕ} {F : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) (hc : 0 < c) (hδ : 0 < δ) :
    0 < ∑ p ∈ a.cell, (p : ℝ)⁻¹ :=
  (by positivity : 0 < δ * c / (32 * Real.exp u)).trans_le a.mass

theorem CharacterAnchorCell.index_le {P : Finset ℕ} {F : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) (hc : 0 < c) (hδ : 0 < δ)
    (B : ℕ) (hP : ∀ p ∈ P, primeLogIndex p ≤ B) : a.index ≤ B := by
  have hn : a.cell.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hm := a.cell_mass_pos hc hδ
    rw [he, Finset.sum_empty] at hm
    exact (lt_irrefl 0) hm
  obtain ⟨p, hp⟩ := hn
  have hi : primeLogIndex p = a.index := (Finset.mem_filter.mp hp).2
  rw [← hi]
  exact hP p (a.cell_subset hp)

theorem CharacterAnchorCell.cell_probability {P : Finset ℕ} {F : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) (hc : 0 < c) (hδ : 0 < δ) :
    ∑ p : P, primeSubsetPrior P a.cell p = 1 := by
  exact primeSubsetPrior_mass P a.cell a.cell_subset (a.cell_mass_pos hc hδ).ne'

theorem CharacterAnchorCell.cell_prime_bounds {P : Finset ℕ} {F : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) (hP : ∀ p ∈ P, p.Prime)
    (p : ℕ) (hp : p ∈ a.cell) :
    primeCellLower a.index ≤ p ∧ p ≤ primeCellUpper a.index :=
  primeCell_interval p a.index (hP p (a.cell_subset hp)) (Finset.mem_filter.mp hp).2

theorem CharacterAnchorCell.unrotated_mean {P : Finset ℕ} {G : ℕ → ℂ} {c δ u : ℝ}
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (a : CharacterAnchorCell P (fun p => ζ * G p) c δ u) :
    δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P a.cell p : ℂ) * G p‖ := by
  have h := a.mean.trans (Complex.re_le_norm _)
  rwa [norm_weighted_common_rotation _ _ ζ hζ] at h

theorem CharacterAnchorCell.cell_mass_exponential {P : Finset ℕ} {F : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) (hc : 0 < c) (hδ : 0 < δ)
    (β L : ℝ) (hu : u ≤ β * L) (hL : -Real.log (δ * c / 32) ≤ L) :
    Real.exp (-(β + 1) * L) ≤ ∑ p ∈ a.cell, (p : ℝ)⁻¹ := by
  apply le_trans _ a.mass
  calc
    _ ≤ Real.exp (Real.log (δ * c / 32) - u) :=
      Real.exp_le_exp.mpr (by nlinarith only [hu, hL])
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by positivity)]; ring

/-- Anchor selection uses the same whole-shell progression theorem as the
pivot words, without clipping either boundary cell. -/
theorem PublishedProgressionInput.character_anchor_cell
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, ‖F p‖ ≤ 1) →
      c ≤ ∑ p ∈ loglogShell P u, (p : ℝ)⁻¹ →
      δ * (∑ p ∈ loglogShell P u, (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P u, (p : ℝ)⁻¹ * (F p).re →
      Nonempty (CharacterAnchorCell P F c δ u) := by
  filter_upwards [P0.rich_anchor_cell c δ hc hδ] with u hu P F hP hF hm hmean
  obtain ⟨h, hlo, hhi, hmass, _, hbias⟩ := hu (loglogShell P u) F
    (fun p hp => hP p (Finset.mem_filter.mp hp).1)
    (fun _ hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => hF p (Finset.mem_filter.mp hp).1) hm hmean
  refine ⟨⟨h, hlo, hhi, hmass, ?_⟩⟩
  rw [primeSubsetPrior_cell_mean P (loglogShell P u) (Finset.filter_subset _ _) h F]
  exact hbias

theorem character_anchor_pair_bound {P : Finset ℕ} {F : ℕ → ℂ} {c δ us ub τ : ℝ}
    (small : CharacterAnchorCell P F c δ us) (big : CharacterAnchorCell P F c δ ub)
    (hs : 3 * Real.exp us ≤ τ) (hb : Real.exp ub ≤ τ) :
    (small.index : ℝ) + big.index ≤ 4 * τ := by
  have hbig := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 3)
  linarith [small.upper, big.upper]

end Ostmann

end OAI
