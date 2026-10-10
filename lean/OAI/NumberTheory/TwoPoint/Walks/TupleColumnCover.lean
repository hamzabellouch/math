import OAI.NumberTheory.TwoPoint.Walks.TupleColumnWords

namespace OAI

/-! Apply the numerical forest cover simultaneously to all actual tuple columns. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def ColumnLowRank {α : Type*} [Fintype α] [DecidableEq α]
    (w : ColumnWordPattern α) (hn : 0 < w.length) (h : ℕ)
    (perfect : Finset (Fin w.length)) (cut : Fin w.length) (r : ℕ) : Prop :=
  ∀ S : Finset (EqualLabelPairs (fun i : perfect.erase cut => w.label i.val.val)), S.card = r →
    ¬LinearIndependent ℝ (pairFamily (labelPairVectors
      (fun i : perfect.erase cut => w.label i.val.val)
      (fun i => formalDeparture (columnNatLabel (fun i : Fin w.length => w.label i.val) hn)
        (fun t => (w.coefficient h t : ℝ)) i.val.val)) S)

/-- A surviving lit numerical word supplies one member of the fixed joint
code universe. Its assumptions are the actual low-rank and arithmetic
conditions; no combinatorial covering assumption is made. -/
theorem tuple_column_array_cover {J R : ℕ} (P : Fin J → Finset ℕ)
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    {h s r : ℕ} {supply : ℕ → ℕ → Prop} {x : ℤ} (hh : 0 < h) (hs : 0 < s)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (hlit : ∀ i ∈ perfect, ((padding i : ℤ) * columnTuple w i) ∣
      x + wordDisplacement h ((columnTupleWord w forward padding).take i.val))
    (heligible : ∀ a ∈ columnTupleWord w forward padding, supply a.tuple a.padding)
    (hq : ∀ a ∈ columnTupleWord w forward padding, 0 < a.padding)
    (hsq : ∀ a ∈ columnTupleWord w forward padding, Squarefree a.tuple)
    (hcard : ∀ a ∈ columnTupleWord w forward padding, a.tuple.primeFactors.card = J)
    (hleft : ((columnTupleWord w forward padding).take cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (hright : ((columnTupleWord w forward padding).drop cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt (columnTupleWord w forward padding) p j →
      ¬p ∣ h ∧ ∀ a ∈ columnTupleWord w forward padding, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x (columnTupleWord w forward padding) y →
      ¬ProhibitedSite h s supply y)
    (L : ℝ) (hL : 1 ≤ L) (hRL : (R : ℝ) ≤ 2 * L)
    (hsL : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hrL : (r : ℝ) ≤ L ^ (1 / 50 : ℝ))
    (hI : (imperfectColumnCount (perfect.erase cut) : ℝ) ≤ 2 * L ^ (1 / 4 : ℝ))
    (hno : ∀ j, ColumnLowRank (tupleColumnPattern w hR forward padding j) hR h perfect cut r) :
    ∃ code : BudgetColumnArrayCode J (2 * R) L,
      ∀ j i l, decodeBudgetColumnArray (show R ≤ 2 * R by omega) code j i l =
        decide (w j i = w j l) := by
  have hcol : ∀ j, ∃ code : BudgetColumnCode (2 * R) L,
      decodeBudgetColumnPattern (show R ≤ 2 * R by omega) code =
        fun i l => decide (w j i = w j l) := by
    intro j
    let c := tupleColumnPattern w hR forward padding j
    have he : c.word Subtype.val = columnTupleWord w forward padding :=
      tupleColumnPattern_word w hR forward padding j
    have hv : Function.Injective (Subtype.val : P j → ℕ) := Subtype.val_injective
    have hp : ∀ p : P j, p.val.Prime := fun p => hprime j _ p.property
    have ho := tupleColumnPattern_not_dvd_other w hR forward padding j hprime (hdisjoint j)
    have ht : ∀ i ∈ perfect, (c.step Subtype.val i.val).divisor ∣
        x + wordDisplacement h ((c.word Subtype.val).take i.val) := by
      intro i hi
      rw [he, tupleColumnPattern_step]
      exact hlit i hi
    obtain ⟨code, hc⟩ := c.numerical_column_in_universe hR Subtype.val hv hp ho hh hs
      perfect cut ht (by simpa only [he] using heligible)
      (by simpa only [he] using hq) (by simpa only [he] using hsq)
      (by simpa only [he] using hcard) (by simpa only [he] using hleft)
      (by simpa only [he] using hright) (by simpa only [he] using hsupport)
      (by simpa only [he] using hsurvive) L hL hRL hsL hrL hI (hno j)
    refine ⟨code, hc.trans ?_⟩
    funext i l
    exact congrArg₂ (fun a b : P j => decide (a = b))
      (tupleColumnPattern_label w hR forward padding j i)
      (tupleColumnPattern_label w hR forward padding j l)
  obtain ⟨code, hc⟩ := budget_column_array_cover (show R ≤ 2 * R by omega)
    (fun j i l => decide (w j i = w j l)) hcol
  exact ⟨code, fun j i l => congrFun (congrFun (congrFun hc j) i) l⟩

end TwoPointCorrelations

end OAI
