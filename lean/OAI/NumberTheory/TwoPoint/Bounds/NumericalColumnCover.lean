import OAI.NumberTheory.TwoPoint.Bounds.MidpointCut
import OAI.NumberTheory.TwoPoint.Bounds.LowRankColumnCover

namespace OAI

/-! A surviving numerical trace word belongs to the universal column code set. -/

namespace TwoPointCorrelations.ColumnWordPattern

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The complete column-covering implication. Only the two halves are
assumed nonbacktracking. All positivity premises are actual divisibilities
at the original perfect positions; one midpoint reference is charged to
the imperfect budget. The finite code universe is independent of `value`,
the signs, the padding, and the fixed other-column coefficients. -/
theorem numerical_column_in_universe (w : ColumnWordPattern α) (hn : 0 < w.length)
    (value : α → ℕ) (hvalue : Function.Injective value) (hprime : ∀ z, (value z).Prime)
    (hother : ∀ z t, t < w.length → ¬value z ∣ w.otherColumns t)
    {h s J r : ℕ} {supply : ℕ → ℕ → Prop} {x : ℤ} (hh : 0 < h) (hs : 0 < s)
    (perfect : Finset (Fin w.length)) (cut : Fin w.length)
    (hlit : ∀ i ∈ perfect, (w.step value i.val).divisor ∣
      x + wordDisplacement h ((w.word value).take i.val))
    (heligible : ∀ a ∈ w.word value, supply a.tuple a.padding)
    (hq : ∀ a ∈ w.word value, 0 < a.padding)
    (hsq : ∀ a ∈ w.word value, Squarefree a.tuple)
    (hcard : ∀ a ∈ w.word value, a.tuple.primeFactors.card = J)
    (hleft : ((w.word value).take cut.val).IsChain (fun a b => a.tuple ≠ b.tuple))
    (hright : ((w.word value).drop cut.val).IsChain (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt (w.word value) p j →
      ¬p ∣ h ∧ ∀ a ∈ w.word value, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x (w.word value) y → ¬ProhibitedSite h s supply y)
    (L : ℝ) (hL : 1 ≤ L) (hnL : (w.length : ℝ) ≤ 2 * L)
    (hsL : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hrL : (r : ℝ) ≤ L ^ (1 / 50 : ℝ))
    (hI : (imperfectColumnCount (perfect.erase cut) : ℝ) ≤ 2 * L ^ (1 / 4 : ℝ))
    (hno : ∀ S : Finset (EqualLabelPairs
        (fun i : perfect.erase cut => w.label i.val.val)), S.card = r →
      ¬LinearIndependent ℝ (pairFamily (labelPairVectors
        (fun i : perfect.erase cut => w.label i.val.val)
        (fun i => formalDeparture (columnNatLabel (fun i : Fin w.length => w.label i.val) hn)
          (fun t => (w.coefficient h t : ℝ)) i.val.val)) S)) :
    ∃ code : BudgetColumnCode (2 * w.length) L,
      decodeBudgetColumnPattern (show w.length ≤ 2 * w.length by omega) code =
        fun i j => decide (w.label i.val = w.label j.val) := by
  have hg := w.short_geometry_of_lit hn value hvalue hprime hother hh (perfect.erase cut)
    (fun i hi => hlit i (mem_of_mem_erase hi)) heligible hq hsq hcard
    (fun start len hend _ hp => trace_perfect_block_chain perfect cut (w.word value)
      hleft hright start len hend hp) hsupport hsurvive
  exact low_rank_column_in_budget_universe (fun i : Fin w.length => w.label i.val) hn
    (fun t => (w.coefficient h t : ℝ)) (perfect.erase cut) s r hs L hL hnL hsL hrL hI hno hg

end TwoPointCorrelations.ColumnWordPattern

end OAI
