import OAI.NumberTheory.Ostmann.Construction.InitialCellPriors
import OAI.NumberTheory.Ostmann.Construction.InitialMixedNormalizer
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantAmbientPrior

namespace OAI

/-! # Probability and point-mass bounds for the selected original half-list -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedInitialHalfPrior (P : Finset ℕ) (A B : Set ℕ)
    (N hi : ℕ) (Y G : ℝ) (D Qb Qd : Finset ℕ) (b d top : ℕ)
    (centers : List ℕ) : Fin ((b + (d + (initialSmallCellList top centers).length)) + 1) → P → ℝ :=
  Fin.cons (smoothGiantPrior P logCellProfile G)
    (Fin.append (fun _ : Fin b => primeSubsetPrior P Qb)
      (Fin.append (fun _ : Fin d => primeSubsetPrior P Qd)
        (fun i => primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D
          ((initialSmallCellList top centers).get i)))))

theorem selected_initial_prior_bounds
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G target g a₀ : ℝ}
    {D Qb Qd : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hsmall : initialRegularPrimeRange L ⊆ P) (hgiant : smoothGiantPrimeRange G ⊆ P)
    (hmass : 0 < smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G)
    (hnorm : smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ g * L)
    (hbmass : ∑ p : P, primeSubsetPrior P Qb p = 1)
    (hdmass : ∑ p : P, primeSubsetPrior P Qd p = 1)
    (hpoint : ∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (a₀ * L)⁻¹ ∧
      (p : ℝ) * primeSubsetPrior P Qd p ≤ (a₀ * L)⁻¹)
    (b d : ℕ) :
    let ν := selectedInitialHalfPrior P A B N hi Y G D Qb Qd b d top centers
    (∀ i p, 0 ≤ ν i p) ∧ (∀ i, ∑ p : P, ν i p = 1) ∧
    (∀ i (p : P), (p : ℝ) * ν i p ≤
      initialHalfNormalizer b d (initialSmallCellList top centers).length a₀ L g i) := by
  intro ν
  have hc (i : Fin (initialSmallCellList top centers).length) :=
    initial_selected_cells_valid htop hcenters _
      (List.get_mem (initialSmallCellList top centers) i)
  have hdata (i : Fin (initialSmallCellList top centers).length) :=
    (hc i).choose_spec.prior_data P
      ((hc i).choose_spec.subset_initialRegularPrimeRange.trans hsmall)
  have he := smoothGiantMass_ambient P hP logCellProfile G logCellProfile_zero_outside hgiant
  have hgmass : ∑ p : P, smoothGiantPrior P logCellProfile G p = 1 :=
    smoothGiantPrior_mass P logCellProfile G (he.symm ▸ hmass)
  have hgnorm : smoothGiantLogNormalizer P logCellProfile G ≤ g * L := by
    simpa only [smoothGiantLogNormalizer, he] using hnorm
  refine ⟨?_, ?_, ?_⟩
  · intro i p
    refine Fin.cases (smoothGiantPrior_nonneg P logCellProfile G logCellProfile_nonneg p)
      (fun j => ?_) i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [ν, selectedInitialHalfPrior, Fin.cons_succ, Fin.append_left] using
        primeSubsetPrior_nonneg P Qb p
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [ν, selectedInitialHalfPrior, Fin.cons_succ, Fin.append_right,
          Fin.append_left] using primeSubsetPrior_nonneg P Qd p
      · simpa only [ν, selectedInitialHalfPrior, Fin.cons_succ, Fin.append_right] using
          ((hdata j).2.1 p).1
  · intro i
    refine Fin.cases hgmass (fun j => ?_) i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [ν, selectedInitialHalfPrior, Fin.cons_succ, Fin.append_left] using hbmass
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [ν, selectedInitialHalfPrior, Fin.cons_succ, Fin.append_right,
          Fin.append_left] using hdmass
      · simpa only [ν, selectedInitialHalfPrior, Fin.cons_succ, Fin.append_right] using
          (hdata j).1
  · apply initialHalfNormalizer_prime_bound
    · intro p
      rw [smoothGiantPrior_cancel_prime P hP]
      exact (mul_le_of_le_one_right (Real.exp_nonneg _) (logCellProfile_le_one _)).trans
        (Real.exp_le_exp.mpr hgnorm)
    · intro _ p
      exact (hpoint p).1
    · intro _ p
      exact (hpoint p).2
    · intro i p
      exact (hdata i).2.1 p |>.2

end Ostmann

end OAI
