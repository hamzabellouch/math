import OAI.NumberTheory.Ostmann.Construction.TailInitialBroadPriors
import OAI.NumberTheory.Ostmann.Construction.InitialCellPriors

namespace OAI

/-! # Constructing the original nongiant priors from the infinite tails -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.constructed_initial_nongiant_priors
    (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
    (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {C : ℝ} (hM : MertensEstimate C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    ∃ a : ℝ, 0 < a ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ Bs BD Bz : ℝ, 0 ≤ Bs → 0 ≤ BD → 0 ≤ Bz →
      ∀ cutoff : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
      ∀ lo G : ℝ,
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → initialRegularPrimeRange L ⊆ P →
      let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      let m := spectatorBulkCount k L
      ∃ Qd : Finset ℕ, ∃ cb cd : ℤ, ∃ top : ℕ, ∃ centers : List ℕ,
        Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
          (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
        L / 320000 ≤ ∑ p ∈ Qd, (p : ℝ)⁻¹ ∧
        (∀ p ∈ Qd, cutoff ≤ p ∧
          ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
            residueDensity (tailDensityMask A N p) ≤ 2 / 3) ∧
          tailCharacterBias A N p ≤ ε / 2) ∧
        cb ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ ∧
        cd ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ ∧
        SelectedSmallTailCell A B N a C L Y hi D
          ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top ∧
        List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
          centers (movingCompensationTargets
            (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
            (movingCompensationGaps k BD Bz L)) ∧
        centers.length = k ∧
        |2 * (G + cb + cd + 3 * top + 2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) -
          (Y + spectatorBaseGap Bs ((k : ℝ) ^ 4) m)| ≤
            (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) ∧
        (∑ p : P, primeSubsetPrior P Qb p) = 1 ∧
        (∑ p : P, primeSubsetPrior P Qd p) = 1 ∧
        (∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (L / 320000)⁻¹ ∧
          (p : ℝ) * primeSubsetPrior P Qd p ≤ (L / 320000)⁻¹) ∧
        let cells := initialSmallCellList top centers
        let μc := fun i : Fin cells.length => primeSubsetPrior P
          (selectedTailCellPrimes A B N Y hi D (cells.get i))
        Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
          ∑ x ∈ balancedTupleSet (m / 2 + (m / 2 + cells.length)) (fun _ (p : P) =>
            (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
              residueDensity (tailDensityMask A N p) ≤ 2 / 3),
            productPrior (Fin.append (fun _ : Fin (m / 2) => primeSubsetPrior P Qb)
              (Fin.append (fun _ : Fin (m / 2) => primeSubsetPrior P Qd) μc)) x *
                initialLogSumWeight (fun p : P => (p : ℕ)) cb
                  (fun i => x (i.castAdd (m / 2 + cells.length))) *
                initialLogSumWeight (fun p : P => (p : ℕ)) cd
                  (fun i => x ((i.castAdd cells.length).natAdd (m / 2))) := by
  classical
  obtain ⟨a, ha, hcells⟩ := h.selected_initial_cells_at P0 hsize hA hB N hN C hM.lower
  refine ⟨a, ha, ?_⟩
  intro k hk Bs BD Bz hBs hBD hBz cutoff ε hε
  filter_upwards [h.initial_broad_prior_centers hBonami P0 H hSiegel sieve hsize hM
    hA hB N hN k cutoff hk ε hε, hcells k hk Bs BD Bz hBs hBD hBz,
    eventually_ge_atTop (0 : ℝ)] with L hbroad hcells hL
  intro Y hYlo hYhi hi hhi lo G hYlo' hYhi' hGlo hGhi D hD P hP hsmallP Qb m
  obtain ⟨Qd, hQd, hmassd, hgood, hpriors⟩ := hbroad Y hYlo hYhi hi hhi D hD
  have hQbP : Qb ⊆ P := (initial_broad_cell_subset L _ _ hL (by norm_num) D).trans hsmallP
  have hQdP : Qd ⊆ P := hQd.trans ((initial_broad_cell_subset L _ _ hL (by norm_num) D).trans hsmallP)
  obtain ⟨hbmass, hdmass, hpoint, cb, hcb, cd, hcd, hb, hd⟩ :=
    hpriors P hP hQbP hQdP
  obtain ⟨top, centers, htop, hcenters, hlen, htotal⟩ :=
    hcells Y hYlo hYhi hi hhi lo G hYlo' hYhi' hGlo hGhi cb cd hcb hcd D hD
  refine ⟨Qd, cb, cd, top, centers, hQd, hmassd, hgood, hcb, hcd,
    htop, hcenters, hlen, htotal, hbmass, hdmass, hpoint, ?_⟩
  exact initial_selected_cells_balanced_mass htop hcenters P hsmallP (m / 2) (m / 2) m Qb Qd cb cd hb hd

end Ostmann

end OAI
