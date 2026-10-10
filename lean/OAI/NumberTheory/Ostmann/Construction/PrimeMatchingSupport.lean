import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchingEnergy
import OAI.NumberTheory.Ostmann.Construction.MatchedCellSupport
import OAI.NumberTheory.Ostmann.Tree.PartitionMatching

namespace OAI

/-! # Restricting the actual diagonal to cell-preserving matchings -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def cellPreservingMatchings {H K : Type*} [Fintype H]
    (label : H → K) : Finset (Equiv.Perm H) :=
  Finset.univ.filter (fun e => ∀ h, label (e h) = label h)

@[simp] theorem mem_cellPreservingMatchings {H K : Type*} [Fintype H]
    (label : H → K) (e : Equiv.Perm H) :
    e ∈ cellPreservingMatchings label ↔ ∀ h, label (e h) = label h := by
  simp [cellPreservingMatchings]

noncomputable def primeMatchingContribution {H D : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (v : D → ℤ) (c : ((H → P) × D) → ℂ)
    (e : Equiv.Perm H) : ℂ :=
  ∑ d : D, ∑ d' : D, if v d = v d' then
    ∑ l : H → P, c (l, d) * conj (c (l ∘ e.symm, d')) else 0

theorem primePermutationCorrelation_fintype {H D : Type*} [Finite H] [Finite D]
    (fH : Fintype H) (fD : Fintype D)
    (P : Finset ℕ) (v : D → ℤ) (c : ((H → P) × D) → ℂ) :
    @primePermutationCorrelation H D fH fD P v c =
      @primePermutationCorrelation H D (Fintype.ofFinite H) (Fintype.ofFinite D) P v c := by
  cases Subsingleton.elim fH (Fintype.ofFinite H)
  cases Subsingleton.elim fD (Fintype.ofFinite D)
  rfl

theorem primeMatchingContribution_fintype {H D : Type*} [Finite H] [Finite D]
    (fH : Fintype H) (fD : Fintype D)
    (P : Finset ℕ) (v : D → ℤ) (c : ((H → P) × D) → ℂ) (e : Equiv.Perm H) :
    @primeMatchingContribution H D fH fD P v c e =
      @primeMatchingContribution H D (Fintype.ofFinite H) (Fintype.ofFinite D) P v c e := by
  cases Subsingleton.elim fH (Fintype.ofFinite H)
  cases Subsingleton.elim fD (Fintype.ofFinite D)
  rfl

theorem cellPreservingMatchings_fintype {H K : Type*} [Finite H]
    (fH : Fintype H) (label : H → K) :
    @cellPreservingMatchings H K fH label =
      @cellPreservingMatchings H K (Fintype.ofFinite H) label := by
  cases Subsingleton.elim fH (Fintype.ofFinite H)
  rfl

theorem primeMatchingContribution_zero_of_changes_cell
    {H D K : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K)
    (hdisjoint : ∀ i j, label i ≠ label j → Disjoint (Q i) (Q j))
    (v : D → ℤ) (c F : ((H → P) × D) → ℂ)
    (hc : ∀ l d, c (l, d) = ((∏ h, primeSubsetPrior P (Q h) (l h) : ℝ) : ℂ) * F (l, d))
    (e : Equiv.Perm H) (he : e ∉ cellPreservingMatchings label) :
    primeMatchingContribution P v c e = 0 := by
  have hn : ∃ i, label (e i) ≠ label i := by
    simpa only [mem_cellPreservingMatchings, not_forall] using he
  obtain ⟨i, hi⟩ := hn
  have hsymm : ∃ j, label (e.symm j) ≠ label j :=
    ⟨e i, by simpa only [e.symm_apply_apply] using hi.symm⟩
  unfold primeMatchingContribution
  apply Finset.sum_eq_zero
  intro d _
  apply Finset.sum_eq_zero
  intro d' _
  split_ifs
  · convert matched_correlation_zero_of_changes_cell P Q label hdisjoint e.symm hsymm
      (fun l => F (l, d) * conj (F (l ∘ e.symm, d'))) using 1
    apply Finset.sum_congr rfl
    intro l _
    rw [hc, hc]
    simp only [map_mul, Complex.conj_ofReal, Function.comp_apply]
    ring
  · rfl

theorem primePermutationCorrelation_cell_support
    {H D K : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K)
    (hdisjoint : ∀ i j, label i ≠ label j → Disjoint (Q i) (Q j))
    (v : D → ℤ) (c F : ((H → P) × D) → ℂ)
    (hc : ∀ l d, c (l, d) = ((∏ h, primeSubsetPrior P (Q h) (l h) : ℝ) : ℂ) * F (l, d)) :
    primePermutationCorrelation P v c =
      ∑ e ∈ cellPreservingMatchings label, primeMatchingContribution P v c e := by
  rw [primePermutationCorrelation_split]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun e _ he =>
    primeMatchingContribution_zero_of_changes_cell P Q label hdisjoint v c F hc e he)).symm

theorem primePermutationCorrelation_cell_split
    {H D K : Type*} [Fintype H] [Fintype D]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K)
    (hdisjoint : ∀ i j, label i ≠ label j → Disjoint (Q i) (Q j))
    (v : D → ℤ) (c F : ((H → P) × D) → ℂ)
    (hc : ∀ l d, c (l, d) = ((∏ h, primeSubsetPrior P (Q h) (l h) : ℝ) : ℂ) * F (l, d))
    (S : Finset (Equiv.Perm H)) (hS : S ⊆ cellPreservingMatchings label) :
    primePermutationCorrelation P v c =
      (∑ e ∈ S, primeMatchingContribution P v c e) +
      ∑ e ∈ cellPreservingMatchings label \ S, primeMatchingContribution P v c e := by
  rw [primePermutationCorrelation_cell_support P Q label hdisjoint v c F hc]
  exact (Finset.sum_sdiff hS).symm.trans (add_comm _ _)

end Ostmann

end OAI
