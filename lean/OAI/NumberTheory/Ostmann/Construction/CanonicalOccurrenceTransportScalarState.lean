import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightState
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportCode
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportSources

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic Arithmetic.HistorySymbolicState
open Characters.RationalHistory

theorem matches_slot_metadata {T : List SourceSlot} {a b : State}
    (ha : Template.Matches T a.small) (hb : Template.Matches T b.small)
    (i : Fin a.small.length) :
    (a.small.get i).role=(b.small.get (finCongr ((Template.matches_length ha).trans
      (Template.matches_length hb).symm) i)).role ∧
    (a.small.get i).origin=(b.small.get (finCongr ((Template.matches_length ha).trans
      (Template.matches_length hb).symm) i)).origin := by
  have hlabels : a.small.map (fun q => (q.role,q.origin))=
      b.small.map (fun q => (q.role,q.origin)) := ha.trans hb.symm
  have he := congrArg (fun xs : List (SlotRole×ℕ) => xs[i.val]?) hlabels
  have hiB : i.val < b.small.length := by
    rw [Template.matches_length hb,← Template.matches_length ha]
    exact i.isLt
  simpa [List.getElem?_eq_getElem,i.isLt,hiB] using he

theorem realStateBins_eq_of_matches {T : List SourceSlot} {a b : State}
    (ha : Template.Matches T a.small) (hb : Template.Matches T b.small)
    (y : Fin a.small.length → ℝ) (z : Fin b.small.length → ℝ)
    (hyz : ∀i,y i=z (finCongr ((Template.matches_length ha).trans
      (Template.matches_length hb).symm) i))
    (bcount scount : ℕ) (tb td : ℝ) (outside : List ℕ) (o : Fin outside.length → ℝ) :
    realStateBins bcount scount tb td a outside y o=
      realStateBins bcount scount tb td b outside z o := by
  classical
  unfold realStateBins
  apply Finset.prod_congr rfl
  intro h hh
  congr 2
  congr 1
  apply Fintype.sum_equiv (finCongr ((Template.matches_length ha).trans
    (Template.matches_length hb).symm))
  intro i
  have hm := matches_slot_metadata ha hb i
  simp only [sourceBulkHalf,hm.1,hm.2,hyz i]

theorem stateCode_small_realEval_eq {ι : Type} {a b : State}
    (e : StateExpr a ι) (f : StateExpr b ι) (hcode : stateCode e=stateCode f)
    (T : List SourceSlot) (ha : Template.Matches T a.small) (hb : Template.Matches T b.small)
    (x : ι → ℝ) (i : Fin a.small.length) :
    (e.small i).realEval x=
      (f.small (finCongr ((Template.matches_length ha).trans (Template.matches_length hb).symm) i)).realEval x := by
  have he := congrArg (fun q : StateCode ι => q.small) hcode
  change List.ofFn e.small=List.ofFn f.small at he
  have hiB : i.val < b.small.length := by
    rw [Template.matches_length hb,← Template.matches_length ha]
    exact i.isLt
  have hv := congrArg (fun xs : List (Expr ι) => xs[i.val]?) he
  have hsmall : e.small i=f.small (finCongr ((Template.matches_length ha).trans
      (Template.matches_length hb).symm) i) := by
    have hi : finCongr ((Template.matches_length ha).trans
        (Template.matches_length hb).symm) i=(⟨i.val,hiB⟩ : Fin b.small.length) := Fin.ext rfl
    rw [hi]
    simpa [List.getElem?_eq_getElem,i.isLt,hiB] using hv
  exact congrArg (fun q => q.realEval x) hsmall

theorem realPeriod_eq_of_stateCode {ι : Type} {a b : State}
    (e : StateExpr a ι) (f : StateExpr b ι) (hcode : stateCode e=stateCode f)
    (outside : List ℕ) (x : ι → ℝ) : e.realPeriod outside x=f.realPeriod outside x := by
  have hp := congrArg (fun q : StateCode ι => q.plus) hcode
  have hm := congrArg (fun q : StateCode ι => q.minus) hcode
  have hs := congrArg (fun q : StateCode ι => q.small) hcode
  change e.plus=f.plus at hp
  change e.minus=f.minus at hm
  change List.ofFn e.small=List.ofFn f.small at hs
  unfold StateExpr.realPeriod
  rw [hp,hm,hs]

theorem realScalar_eq_of_stateCode {ι : Type} {a b : State}
    (e : StateExpr a ι) (f : StateExpr b ι) (hcode : stateCode e=stateCode f)
    (T : List SourceSlot) (ha : Template.Matches T a.small) (hb : Template.Matches T b.small)
    (hfreq : a.frequency=b.frequency) (bcount scount : ℕ) (X tb td : ℝ)
    (outside : List ℕ) (x : ι → ℝ) :
    e.realScalar bcount scount X tb td outside x=f.realScalar bcount scount X tb td outside x := by
  have hperiod := realPeriod_eq_of_stateCode e f hcode outside x
  have hbins := realStateBins_eq_of_matches ha hb
    (fun i => (e.small i).realEval x) (fun i => (f.small i).realEval x)
    (stateCode_small_realEval_eq e f hcode T ha hb x) bcount scount tb td outside
    (fun i => (outside.get i:ℝ))
  unfold StateExpr.realScalar
  rw [hperiod,hfreq,hbins]

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
