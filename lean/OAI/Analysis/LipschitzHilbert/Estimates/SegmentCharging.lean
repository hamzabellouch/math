import OAI.Analysis.LipschitzHilbert.Estimates.MarkedShells

namespace OAI

/-!
# Charging unary segments to positive mass drops

This is the finite counting argument in §10 `res:segment-shell-count`.
Completed segments charge their starting drop, and remainders charge
the next interruption. The charge can lie at most two units of mass
below the segment start. Injectivity permits one final uncharged segment.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

/-- An injective optional charge permits one final remainder and no
multiplicity depending on the number of unary levels. -/
theorem charged_segment_shell_card {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (charge : ι → Option ℕ) (n : ℕ → ℝ)
    (hn : Antitone n) (hinj : Function.Injective charge)
    {c a b : ℝ} (hc : 0 < c) (hab : a ≤ b)
    (hcharge : ∀ i k, charge i = some k →
      mass i - 2 ≤ n k ∧ n k ≤ mass i ∧ c ≤ n k - n (k + 1))
    (S : Finset ι) (hS : ∀ i ∈ S, a ≤ mass i ∧ mass i ≤ b) :
    (S.card : ℝ) ≤ 2 + (b - a + 2) / c := by
  classical
  let T := S.filter (fun i => charge i ≠ none)
  have hsome (i : T) : charge i = some ((charge i).getD 0) := by
    cases hi : charge i with
    | none => exact False.elim ((Finset.mem_filter.mp i.property).2 hi)
    | some k => simp
  have hindex : Function.Injective (fun i : T => (charge i).getD 0) := by
    intro i j hij
    apply Subtype.ext
    apply hinj
    exact (hsome i).trans ((congrArg some hij).trans (hsome j).symm)
  have hbound (i : T) : a - 2 ≤ n ((charge i).getD 0) ∧ n ((charge i).getD 0) ≤ b := by
    have hiS := (Finset.mem_filter.mp i.property).1
    have hi := hcharge i _ (hsome i)
    exact ⟨by linarith [(hS i hiS).1, hi.1], hi.2.1.trans (hS i hiS).2⟩
  have hsep : Separated (fun i : T => n ((charge i).getD 0)) c := by
    intro i j hij
    have hne : (charge i).getD 0 ≠ (charge j).getD 0 := fun h => hij (hindex h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hd := (hcharge i _ (hsome i)).2.2
      have hm := hn (show (charge i).getD 0 + 1 ≤ (charge j).getD 0 by omega)
      have hm' := hn hlt.le
      rw [abs_of_nonneg (sub_nonneg.mpr hm')]
      linarith
    · have hd := (hcharge j _ (hsome j)).2.2
      have hm := hn (show (charge j).getD 0 + 1 ≤ (charge i).getD 0 by omega)
      have hm' := hn hgt.le
      rw [abs_of_nonpos (sub_nonpos.mpr hm')]
      linarith
  have hT : (T.card : ℝ) ≤ 1 + (b - a + 2) / c := by
    have h := separated_card_le_span (fun i : T => n ((charge i).getD 0)) hc
      (show a - 2 ≤ b by linarith) hsep hbound
    have heq : b - (a - 2) = b - a + 2 := by ring
    simpa only [Fintype.card_coe, heq] using h
  have hnone : (S.filter (fun i => charge i = none)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hinj ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun i => charge i = none)
  have hcount : S.card ≤ T.card + 1 := by
    dsimp [T]
    omega
  exact (show (S.card : ℝ) ≤ (T.card : ℝ) + 1 by exact_mod_cast hcount).trans (by linarith)

/-- A ratio-sixteen shell has a linear cardinal bound with an absolute
coefficient depending only on the fixed minimum interruption drop. -/
theorem charged_segment_shell_linear {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (charge : ι → Option ℕ) (n : ℕ → ℝ)
    (hn : Antitone n) (hinj : Function.Injective charge)
    {c t : ℝ} (hc : 0 < c) (ht : 1 ≤ t)
    (hcharge : ∀ i k, charge i = some k →
      mass i - 2 ≤ n k ∧ n k ≤ mass i ∧ c ≤ n k - n (k + 1))
    (S : Finset ι) (hS : ∀ i ∈ S, t ≤ mass i ∧ mass i ≤ 16 * t) :
    (S.card : ℝ) ≤ (2 + 17 / c) * t := by
  have h := charged_segment_shell_card mass charge n hn hinj hc
    (show t ≤ 16 * t by linarith) hcharge S hS
  apply h.trans
  have hdiv : 0 ≤ (t - 1) / c := div_nonneg (by linarith) hc.le
  have hid : (2 + 17 / c) * t - (2 + (16 * t - t + 2) / c) =
      2 * (t - 1) + 2 * ((t - 1) / c) := by ring
  linarith

end LipschitzHilbert

end

end OAI
