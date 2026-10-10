import OAI.Combinatorics.ProgressionColoring.FairOuterColoring
import OAI.Combinatorics.ProgressionColoring.OuterIncidence
import Mathlib.Data.Fintype.BigOperators

namespace OAI

universe uG uL uLabel

namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem outer_sum_incident_split
    {G : Type uG} {L : Type uL} {Label : Type uLabel} [Fintype G] [Fintype L] [DecidableEq G] [DecidableEq L]
    [DecidableEq Label] (gsupport : G → Finset Label) (lsupport : L → Finset Label)
    (b : Label) :
    (∑ i ∈ Finset.univ.filter (fun i : G ⊕ L => b ∈ Sum.elim gsupport lsupport i),
      Real.exp (-((Sum.elim gsupport lsupport i).card : ℝ) / 32)) =
      (∑ i ∈ Finset.univ.filter (fun i => b ∈ gsupport i),
        Real.exp (-((gsupport i).card : ℝ) / 32)) +
      (∑ i ∈ Finset.univ.filter (fun i => b ∈ lsupport i),
        Real.exp (-((lsupport i).card : ℝ) / 32)) := by
  classical
  simp only [Finset.sum_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  apply congrArg₂ (fun x y : ℝ => x + y)
  · refine Finset.sum_congr ?_ ?_
    · apply Finset.ext
      intro i
      simp only [Finset.mem_univ]
    · intro i _
      by_cases hi : b ∈ gsupport i <;> simp only [hi, ite_true, ite_false]
  · refine Finset.sum_congr ?_ ?_
    · apply Finset.ext
      intro i
      simp only [Finset.mem_univ]
    · intro i _
      by_cases hi : b ∈ lsupport i <;> simp only [hi, ite_true, ite_false]

theorem exists_outer_coloring_of_family_counts
    {G : Type uG} {L : Type uL} {Label : Type uLabel} [Fintype G] [Fintype L] [DecidableEq G] [DecidableEq L]
    [Fintype Label] [DecidableEq Label]
    (gsupport : G → Finset Label) (lsupport : L → Finset Label)
    (period : L → ℕ) (periods : Finset ℕ) (countBound : ℕ → ℕ)
    (rowLower : ℝ) (hrowLower : 100 ≤ rowLower)
    (hgsize : ∀ i, rowLower ≤ ((gsupport i).card : ℝ))
    (hlsize : ∀ i, (100 : ℝ) ≤ (lsupport i).card)
    (hperiod : ∀ i, period i ∈ periods)
    (hhalf : ∀ i, period i ≤ 2 * (lsupport i).card)
    (hcount : ∀ b h,
      (Finset.univ.filter (fun i => b ∈ lsupport i ∧ period i = h)).card ≤ countBound h)
    (hbudget : (Fintype.card G : ℝ) * Real.exp (-rowLower / 32) +
      (∑ h ∈ periods, (countBound h : ℝ) * Real.exp (-(h : ℝ) / 64)) ≤ 1 / 500) :
    ∃ color : Label → Bool,
      (∀ i b, (gsupport i).card ≤
        4 * ((gsupport i).filter fun a => color a = b).card) ∧
      (∀ i b, (lsupport i).card ≤
        4 * ((lsupport i).filter fun a => color a = b).card) := by
  classical
  let support : G ⊕ L → Finset Label := Sum.elim gsupport lsupport
  have hsize : ∀ i, (100 : ℝ) ≤ (support i).card := by
    intro i
    cases i with
    | inl i => exact hrowLower.trans (hgsize i)
    | inr i => exact hlsize i
  have hincident : ∀ b,
      ∑ i ∈ Finset.univ.filter (fun i => b ∈ support i),
        Real.exp (-((support i).card : ℝ) / 32) ≤ 1 / 500 := by
    intro b
    have hglobal : (∑ i ∈ Finset.univ.filter (fun i => b ∈ gsupport i),
        Real.exp (-((gsupport i).card : ℝ) / 32)) ≤
        (Fintype.card G : ℝ) * Real.exp (-rowLower / 32) := by
      calc
        _ ≤ ∑ i : G, Real.exp (-((gsupport i).card : ℝ) / 32) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => (Real.exp_pos _).le)
        _ ≤ (Fintype.card G : ℝ) * Real.exp (-rowLower / 32) := by
          simpa only [Finset.card_univ] using
            outer_total_weight_bound Finset.univ gsupport rowLower (fun i _ => hgsize i)
    have hlocal := outer_local_incident_bound lsupport period periods countBound
      hperiod hhalf hcount b
    dsimp only [support]
    rw [outer_sum_incident_split]
    exact (add_le_add hglobal hlocal).trans hbudget
  obtain ⟨color, hcolor⟩ := exists_fair_balancing_coloring support hsize hincident
  exact ⟨color, (fun i b => hcolor (Sum.inl i) b),
    (fun i b => hcolor (Sum.inr i) b)⟩

end QuantitativeVanDerWaerden

end OAI
