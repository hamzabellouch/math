import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkDecode
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyLeaves

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts HistoryLinearization CanonicalHistoryLeafBulk

theorem frequencyLeaves_eq_of_leaf_bulkProduct_eq (Q : ℕ) {l : ℕ}
    (h h' : History l)
    (hbulk : ∀ path : Tree.Leaves l,
      bulkProduct (leafStateAt h path).small = bulkProduct (leafStateAt h' path).small) :
    frequencyLeaves Q h = frequencyLeaves Q h' := by
  induction h with
  | leaf a =>
    cases h' with
    | leaf a' =>
      have he := hbulk (fun i => Fin.elim0 i)
      change bulkProduct a.small = bulkProduct a'.small at he
      simp only [frequencyLeaves, he]
  | @node l a pivot u hp hm left right ihl ihr =>
    cases h' with
    | node a' pivot' u' hp' hm' left' right' =>
      apply Prod.ext
      · apply ihl left'
        intro path
        simpa only [leafStateAt, Fin.cons_zero, Bool.false_eq_true, ite_false,
          Fin.tail_cons] using hbulk (Fin.cons false path)
      · apply ihr right'
        intro path
        simpa only [leafStateAt, Fin.cons_zero, ite_true, Fin.tail_cons] using
          hbulk (Fin.cons true path)

theorem decodeHistory_frequencyLeaves_eq_of_small_eq {Q : ℕ}
    (sources : SourceFamily) (m k : ℕ) (V : ℕ → ℕ) (l : ℕ) (a a' : State)
    (c e : HistoryChoices sources (Template.initial m k) V l)
    (ha : Template.Matches (Template.current (Template.initial m k) l) a.small)
    (hsmall : a.small = a'.small) :
    frequencyLeaves Q (decodeHistory sources (Template.initial m k) V l a c) =
      frequencyLeaves Q (decodeHistory sources (Template.initial m k) V l a' e) := by
  have ha' : Template.Matches (Template.current (Template.initial m k) l) a'.small := by
    rw [← hsmall]
    exact ha
  apply frequencyLeaves_eq_of_leaf_bulkProduct_eq
  intro path
  change (bulkValues (leafStateAt (decodeHistory sources (Template.initial m k) V l a c)
    path).small).prod = (bulkValues (leafStateAt
      (decodeHistory sources (Template.initial m k) V l a' e) path).small).prod
  rw [decodeHistory_bulkValues sources m k V l a c ha path,
    decodeHistory_bulkValues sources m k V l a' e ha' path, hsmall]

theorem decodeHistory_frequencyLeaves_eq {Q : ℕ}
    (sources : SourceFamily) (m k : ℕ) (V : ℕ → ℕ) (l : ℕ) (a : State)
    (c e : HistoryChoices sources (Template.initial m k) V l)
    (ha : Template.Matches (Template.current (Template.initial m k) l) a.small) :
    frequencyLeaves Q (decodeHistory sources (Template.initial m k) V l a c) =
      frequencyLeaves Q (decodeHistory sources (Template.initial m k) V l a e) :=
  decodeHistory_frequencyLeaves_eq_of_small_eq sources m k V l a a c e ha rfl

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
