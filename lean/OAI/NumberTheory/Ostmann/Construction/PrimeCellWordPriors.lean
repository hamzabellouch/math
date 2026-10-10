import OAI.NumberTheory.Ostmann.Construction.ComplexCellMeans
import OAI.NumberTheory.Ostmann.Construction.RichPrimeCellTargets
import OAI.NumberTheory.Ostmann.Construction.PositiveWordBins

namespace OAI

/-! # The original harmonic law on each selected prime cell -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def primeCellWordPrior (P : Finset ℕ) (h : ℕ) (p : P) : ℝ :=
  if primeLogIndex p = h then
    ((p : ℕ) : ℝ)⁻¹ / finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h else 0

theorem primeCellWordPrior_nonneg (P : Finset ℕ) (h : ℕ) (p : P) :
    0 ≤ primeCellWordPrior P h p := by
  unfold primeCellWordPrior
  split_ifs
  · exact div_nonneg (by positivity) (finiteCellMass_nonneg P _ _ (by intros; positivity) h)
  · exact le_rfl

theorem primeCellWordPrior_mass (P : Finset ℕ) (h : ℕ)
    (hmass : finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h ≠ 0) :
    (∑ p : P, primeCellWordPrior P h p) = 1 := by
  unfold primeCellWordPrior
  rw [Finset.sum_coe_sort P (fun p => if primeLogIndex p = h then
    (p : ℝ)⁻¹ / finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h else 0)]
  rw [← Finset.sum_filter, ← Finset.sum_div]
  exact div_self hmass

theorem primeCellWordPrior_mean (P : Finset ℕ) (h : ℕ) (F : ℕ → ℂ) :
    (∑ p : P, (primeCellWordPrior P h p : ℂ) * F p) =
      complexCellMean P primeLogIndex (fun p => (p : ℝ)⁻¹) F h := by
  unfold primeCellWordPrior
  simp only [apply_ite, Complex.ofReal_div, Complex.ofReal_zero, ite_mul, zero_mul]
  rw [Finset.sum_coe_sort P (fun p => if primeLogIndex p = h then
    (((p : ℝ)⁻¹ : ℝ) : ℂ) / (finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h : ℂ) * F p else 0)]
  rw [← Finset.sum_filter]
  unfold complexCellMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem primeCellWordPrior_support (P : Finset ℕ) (h : ℕ) (p : P)
    (hp : primeCellWordPrior P h p ≠ 0) : primeLogIndex p = h := by
  by_contra hn
  simp [primeCellWordPrior, hn] at hp

/-- The selected cells carry genuine probability laws with the claimed
positive complex means, so they can be used directly in independent words. -/
theorem PublishedProgressionInput.rich_prime_word_priors
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, B ≤ primeLogIndex p ∧ (primeLogIndex p : ℝ) ≤ 3 * B) →
      (∀ p ∈ P, ‖F p‖ ≤ 1) → c ≤ ∑ p ∈ P, (p : ℝ)⁻¹ →
      δ * (∑ p ∈ P, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ * (F p).re →
      ∀ T : ℝ, C * B ≤ T → ∃ (n : ℕ) (w : List ℕ),
        w.length = n ∧
        (∀ h ∈ w,
          δ * c / (32 * B) ≤ finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h ∧
          (∑ p : P, primeCellWordPrior P h p) = 1 ∧
          δ / 2 ≤ (∑ p : P, (primeCellWordPrior P h p : ℂ) * F p).re) ∧
        |(w.sum : ℝ) - T| < 64 / (δ * c) ∧
        (n : ℝ) * B ≤ 128 / (δ * c) * T := by
  obtain ⟨C, hC, htargets⟩ := P0.rich_prime_cell_targets c δ hc hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [htargets, eventually_gt_atTop (0 : ℝ)] with B htargets hB P F hP hlabel hF hmass hbias T hT
  obtain ⟨n, w, hlen, hcells, herr, hn⟩ := htargets P (fun p => (F p).re) hP hlabel
    (fun p hp => (Complex.re_le_norm _).trans (hF p hp)) hmass hbias T hT
  refine ⟨n, w, hlen, ?_, herr, hn⟩
  intro h hh
  have hcell := hcells h hh
  have hpos : 0 < finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h :=
    lt_of_lt_of_le (by positivity) hcell.1
  refine ⟨hcell.1, primeCellWordPrior_mass P h hpos.ne', ?_⟩
  rw [primeCellWordPrior_mean, complexCellMean_re]
  exact hcell.2

end Ostmann

end OAI
