import OAI.NumberTheory.Ostmann.Construction.BadPrimeLogCells

namespace OAI

/-! # A cell outside the imbalance failures retains harmonic mass -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem prime_log_cell_good_mass (I badPrimes : Finset ℕ) (h : ℕ)
    (hhI : h ∈ I) (hh1 : 1 ≤ h) (hgood : h ∉ badPrimeLogCells I badPrimes)
    (hfull : 1 / (2 * ((h : ℝ) + 1)) ≤
      ∑ p ∈ primeLogCellSet 1 0 h ((h : ℝ) + 1), (p : ℝ)⁻¹) :
    1 / (4 * ((h : ℝ) + 1)) ≤
      ∑ p ∈ primeLogCellSet 1 0 h ((h : ℝ) + 1) \ badPrimes, (p : ℝ)⁻¹ := by
  let Q := primeLogCellSet 1 0 h ((h : ℝ) + 1)
  have hsmall : finiteCellMass badPrimes primeLogIndex (fun p => (p : ℝ)⁻¹) h <
      1 / (8 * ((h : ℝ) + 1)) := by
    by_contra! hn
    exact hgood (Finset.mem_filter.mpr ⟨hhI, hh1, hn⟩)
  have hsub : Q.filter (fun p => p ∈ badPrimes) ⊆
      badPrimes.filter (fun p => primeLogIndex p = h) := by
    intro p hp
    obtain ⟨hpQ, hpB⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpP, _, hpL⟩ := mem_primeLogCellSet_iff.mp hpQ
    exact Finset.mem_filter.mpr ⟨hpB, (primeLogIndex_eq_iff p h hpP).mpr hpL⟩
  have hbad : (∑ p ∈ Q.filter (fun p => p ∈ badPrimes), (p : ℝ)⁻¹) <
      1 / (8 * ((h : ℝ) + 1)) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans_lt hsmall
  have hsplit : (∑ p ∈ Q, (p : ℝ)⁻¹) =
      (∑ p ∈ Q \ badPrimes, (p : ℝ)⁻¹) +
        ∑ p ∈ Q.filter (fun p => p ∈ badPrimes), (p : ℝ)⁻¹ := by
    simp only [Finset.sdiff_eq_filter, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p ∈ badPrimes <;> simp [hp]
  have hidentity : 1 / (2 * ((h : ℝ) + 1)) =
      2 * (1 / (4 * ((h : ℝ) + 1))) ∧
      1 / (8 * ((h : ℝ) + 1)) = (1 / (4 * ((h : ℝ) + 1))) / 2 := by
    constructor <;> field_simp <;> ring
  have hpos : 0 ≤ 1 / (4 * ((h : ℝ) + 1)) := by positivity
  change 1 / (4 * ((h : ℝ) + 1)) ≤ ∑ p ∈ Q \ badPrimes, (p : ℝ)⁻¹
  change 1 / (2 * ((h : ℝ) + 1)) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ at hfull
  rw [hidentity.1] at hfull
  rw [hidentity.2] at hbad
  linarith

theorem PublishedProgressionInput.good_prime_log_cell_mass (P : PublishedProgressionInput) :
    ∃ H : ℝ, ∀ (h : ℕ), H ≤ h → ∀ I badPrimes : Finset ℕ,
      h ∈ I → h ∉ badPrimeLogCells I badPrimes →
      1 / (4 * ((h : ℝ) + 1)) ≤
        ∑ p ∈ primeLogCellSet 1 0 h ((h : ℝ) + 1) \ badPrimes, (p : ℝ)⁻¹ := by
  obtain ⟨H, hH⟩ := eventually_atTop.mp P.ordinary_interval_lower
  refine ⟨max H 1, ?_⟩
  intro h hh I badPrimes hhI hgood
  have hh1 : 1 ≤ h := by exact_mod_cast (le_max_right H 1).trans hh
  apply prime_log_cell_good_mass I badPrimes h hhI hh1 hgood
  rw [sum_primeLogCellSet_reciprocal]
  exact hH h ((le_max_left H 1).trans hh)

end Ostmann

end OAI
