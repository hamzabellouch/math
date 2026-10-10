import OAI.NumberTheory.Ostmann.Construction.TailCellWindow
import OAI.NumberTheory.Ostmann.Construction.SelectedCellMassRate

namespace OAI

/-! # Selected small-cell priors for the actual decomposition -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.selected_tail_cells_at
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ X : ℝ, Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp X →
      ∀ target : ℝ, Real.exp ((1 / 100 : ℝ) * L) ≤ target →
        target ≤ Real.exp ((105 / 10000 : ℝ) * L) →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∃ j : ℕ, target ≤ j ∧ (j : ℝ) ≤ target + 64 * tailDefectBudget a C X + 1 ∧
        (j : ℝ) + 1 ≤ Real.exp ((11 / 1000 : ℝ) * L) ∧
        let Q := (primeLogCellSet 1 0 j ((j : ℝ) + 1) \
          tailCellExceptionalPrimes A B N (summandTailCutoff X) hi (tailCollisionCutoff X)) \ D
        Real.exp (-(2 * L)) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) ∧
        0 < (∑ p ∈ Q, (p : ℝ)⁻¹) ∧
        (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * L) ∧
        (∀ p ∈ Q, p.Prime ∧ Real.exp (j : ℝ) < p ∧
          (p : ℝ) ≤ Real.exp ((j : ℝ) + 1) ∧
          (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
          ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  obtain ⟨a, ha, H, hcells⟩ := h.tail_good_prime_cells_at P0 hsize hA hB N hN C hM
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hcells
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  refine ⟨a, ha, ?_⟩
  filter_upwards [eventual_tail_cell_window a C H, eventual_selected_cell_upper a C,
    selected_cell_after_finite_deletion,
    ht.eventually (eventually_ge_atTop X₀), eventually_ge_atTop (0 : ℝ)] with L hwindow hrange hmass hlarge hL
  intro X hXlo hXhi hi hhi target htlo hthi D hD
  have hthi' : target ≤ Real.exp ((11 / 1000 : ℝ) * L) := hthi.trans
    (Real.exp_le_exp.mpr (by nlinarith only [hL]))
  obtain ⟨hH, hcut, hsmall⟩ := hwindow X target hXlo hXhi htlo hthi'
  obtain ⟨j, hjlo, hjhi, hjmass, hjbalanced⟩ :=
    hX₀ X (hlarge.trans hXlo) hi hhi target hH hcut
  have hjrange : (j : ℝ) + 1 ≤ Real.exp ((11 / 1000 : ℝ) * L) := by
    have hx : 0 < X := (Real.exp_pos _).trans_le hXlo
    have hr := hrange X target hx hXhi hthi
    linarith
  let S := primeLogCellSet 1 0 j ((j : ℝ) + 1) \
    tailCellExceptionalPrimes A B N (summandTailCutoff X) hi (tailCollisionCutoff X)
  have hjlower : Real.exp ((39 / 10000 : ℝ) * L) ≤ j := by
    apply le_trans _ (htlo.trans hjlo)
    apply Real.exp_le_exp.mpr
    nlinarith only [hL]
  have hjupper : (j : ℝ) ≤ Real.exp (L / 2) := hjhi.trans hsmall
  have hS : S ⊆ primeLogCellSet 1 0 j ((j : ℝ) + 1) := Finset.sdiff_subset
  obtain ⟨hm, hmpos, hnorm⟩ := hmass j S D hjlower hjupper hS hjmass hD
  refine ⟨j, hjlo, hjhi, hjrange, hm, hmpos, hnorm, ?_⟩
  intro p hp
  have hpS := (Finset.mem_sdiff.mp hp).1
  have hpCell := hS hpS
  obtain ⟨hpp, _, hplo, hphi⟩ := mem_primeLogCellSet_iff.mp hpCell
  refine ⟨hpp, ?_, ?_, hjbalanced p hpS⟩
  · exact (Real.lt_log_iff_exp_lt (by exact_mod_cast hpp.pos)).mp hplo
  · exact (Real.log_le_iff_le_exp (by exact_mod_cast hpp.pos)).mp hphi

theorem EventuallyPrimeSumset.selected_tail_cells
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ N : ℕ, ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ X : ℝ, Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp X →
      ∀ target : ℝ, Real.exp ((1 / 100 : ℝ) * L) ≤ target →
        target ≤ Real.exp ((105 / 10000 : ℝ) * L) →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∃ j : ℕ, target ≤ j ∧ (j : ℝ) ≤ target + 64 * tailDefectBudget a C X + 1 ∧
        (j : ℝ) + 1 ≤ Real.exp ((11 / 1000 : ℝ) * L) ∧
        let Q := (primeLogCellSet 1 0 j ((j : ℝ) + 1) \
          tailCellExceptionalPrimes A B N (summandTailCutoff X) hi (tailCollisionCutoff X)) \ D
        Real.exp (-(2 * L)) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) ∧
        0 < (∑ p ∈ Q, (p : ℝ)⁻¹) ∧
        (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * L) ∧
        (∀ p ∈ Q, p.Prime ∧ Real.exp (j : ℝ) < p ∧
          (p : ℝ) ≤ Real.exp ((j : ℝ) + 1) ∧
          (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
          ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  obtain ⟨N, hN⟩ := h.disjoint_tail_residues
  obtain ⟨a, ha, hrest⟩ := h.selected_tail_cells_at P0 hsize hA hB N hN C hM
  exact ⟨N, a, ha, hrest⟩

end Ostmann

end OAI
