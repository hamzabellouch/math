import OAI.NumberTheory.Ostmann.Construction.InitialProtectedTarget
import OAI.NumberTheory.Ostmann.Construction.SelectedInitialTotal
import OAI.NumberTheory.Ostmann.Construction.InitialSmallCellList
import OAI.NumberTheory.Ostmann.Construction.TailFourierMass
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # Top and compensation cells for the actual initial cutoff centers -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.selected_initial_cells_at
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ a : ℝ, 0 < a ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ Bs BD Bz : ℝ, 0 ≤ Bs → 0 ≤ BD → 0 ≤ Bz →
      ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
      ∀ lo G : ℝ,
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      ∀ cb cd : ℤ,
      cb ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ →
      cd ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      let J := movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L)
      ∃ top : ℕ, ∃ centers : List ℕ,
        SelectedSmallTailCell A B N a C L Y hi D ((J - 2 * cb) / 6) top ∧
        List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
          centers (movingCompensationTargets J (movingCompensationGaps k BD Bz L)) ∧
        centers.length = k ∧
        |2 * (G + cb + cd + 3 * top +
            2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) -
              (Y + spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L))| ≤
          (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) := by
  obtain ⟨a, ha, hcells⟩ := h.selected_compensation_cells_at P0 hsize hA hB N hN C hM
  refine ⟨a, ha, ?_⟩
  intro k hk Bs BD Bz hBs hBD hBz
  filter_upwards [hcells k (by omega) BD Bz hBD hBz,
    eventual_initial_protected_target k hk Bs BD Bz hBs hBD hBz] with L hcells htarget
  intro Y hYlo hYhi hi hhi lo G hYlo' hYhi' hGlo hGhi cb cd hcb hcd D hD J
  obtain ⟨hJlo, hJhi, hcb0, hcbJ⟩ := htarget cb cd hcb hcd lo G Y hYlo' hYhi' hGlo hGhi
  obtain ⟨top, centers, htop, hcenters⟩ :=
    hcells Y hYlo hYhi hi hhi J (2 * cb) hJlo hJhi hcb0 hcbJ D hD
  refine ⟨top, centers, htop, hcenters, ?_, ?_⟩
  · simpa only [movingCompensationTargets_length, movingCompensationGaps_length]
      using hcenters.length_eq
  · exact selected_initial_total_error k htop hcenters

theorem SelectedSmallTailCell.prior_data
    {A B : Set ℕ} {N hi j : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L Y hi D target j)
    (P : Finset ℕ) (hQP : selectedTailCellPrimes A B N Y hi D j ⊆ P) :
    let Q := selectedTailCellPrimes A B N Y hi D j
    (∑ p : P, primeSubsetPrior P Q p) = 1 ∧
    (∀ p : P, 0 ≤ primeSubsetPrior P Q p ∧
      (p : ℝ) * primeSubsetPrior P Q p ≤ Real.exp (2 * L)) ∧
    (∀ p : P, primeSubsetPrior P Q p ≠ 0 →
      (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3) := by
  intro Q
  obtain ⟨_, _, _, _, hpos, hinv, hsupport⟩ := h
  refine ⟨primeSubsetPrior_mass P Q hQP hpos.ne', ?_, ?_⟩
  · intro p
    refine ⟨primeSubsetPrior_nonneg P Q p, ?_⟩
    by_cases hp : (p : ℕ) ∈ Q
    · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hsupport p hp).1.ne_zero
      calc
        _ ≤ (p : ℝ) * ((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left (primeSubsetPrior_atom P Q p) (Nat.cast_nonneg _)
        _ = (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ := by field_simp
        _ ≤ _ := hinv
    · simp only [primeSubsetPrior, hp, ite_false, mul_zero]
      positivity
  · intro p hp
    have hs := hsupport p (primeSubsetPrior_support P Q p hp)
    exact (tailDensityMask_balanced_iff A N p hs.1.pos).mpr ⟨hs.2.2.2.1, hs.2.2.2.2⟩

end Ostmann

end OAI
