import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanDecoded
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanPositiveScalar
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanSample

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction Construction.CanonicalOccurrenceTransport Characters.RationalHistory
open HistorySignedDecode HistorySignedNumerators HistoryOccurrenceVariables HistorySymbolicEncoding

theorem referenceScalar_ne_zero_new_pivotsPositive
    (bSize s : ℕ) (X tb td G : ℝ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (Xp Xm : ℤ)
    (hi : (rebuild (decodeHistory sources seed V l b c) Xp Xm).IntegralGuard)
    (hz : actualRealHistoryScalar bSize s X tb td G outside
      (decodeHistory sources seed V l a c) hs
      (fun k => (newSourceSample sources seed V l b c hb Xp Xm
        ((decodedCoordinateEquiv sources seed V l a c ha).symm k):ℝ))≠0) :
    (rebuild (decodeHistory sources seed V l b c) Xp Xm).PivotsPositive := by
  let h := decodeHistory sources seed V l b c
  let hh := decoded_tree_source_labels sources seed V l b c hb
  let comp : InternalKey h → Expr (Coordinate seed l) :=
    fun j => .atom (.inr (.inr ((internalEquiv seed h hh).symm j)))
  have hc (j : InternalKey h) :
      (comp j).rationalEval (newSourceSample sources seed V l b c hb Xp Xm)=
        ((internalSlot h j).value:ℚ) := by
    change signedRationalSample h Xp Xm
      (.inr (.inr ((internalEquiv seed h hh) ((internalEquiv seed h hh).symm j))))=_
    rw [Equiv.apply_symm_apply]
    rfl
  have he := execute_pivotsPositive_iff_rebuild h
    (plan (decodeHistory sources seed V l a c) hs)
    (decoded_reference_plan_fits sources seed V outside l a b c ha hb hab hs)
    (fixedRootCode seed l) comp (newSourceSample sources seed V l b c hb Xp Xm)
    Xp Xm rfl rfl
    (by simpa only [h,decodeHistory_root] using
      fixedRootCode_newSourceSample_small sources seed V l b c hb Xp Xm) hc hi
  have hcomp : compensationCode h comp=
      fixedCompensationCode seed l (fun i => .atom (.inr (.inr i))) :=
    compensation_code_fixed seed h hh (fun i => (Expr.atom (.inr (.inr i)) : Expr (Coordinate seed l)))
  rw [hcomp] at he
  apply he.mp
  exact codePivotsPositive_execute_of_actualRealHistoryScalar_ne_zero
    bSize s X tb td G outside seed (decodeHistory sources seed V l a c) hs
    (decoded_tree_source_labels sources seed V l a c ha)
    (newSourceSample sources seed V l b c hb Xp Xm) hz

theorem referenceScalar_ne_zero_new_positiveIntegral
    (bSize s : ℕ) (X tb td G : ℝ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (Xp Xm : ℤ) (hp : 0<Xp) (hm : 0<Xm)
    (hi : (rebuild (decodeHistory sources seed V l b c) Xp Xm).IntegralGuard)
    (hz : actualRealHistoryScalar bSize s X tb td G outside
      (decodeHistory sources seed V l a c) hs
      (fun k => (newSourceSample sources seed V l b c hb Xp Xm
        ((decodedCoordinateEquiv sources seed V l a c ha).symm k):ℝ))≠0) :
    (rebuild (decodeHistory sources seed V l b c) Xp Xm).PositiveIntegral :=
  rebuild_positiveIntegral _ Xp Xm hp hm hi
    (referenceScalar_ne_zero_new_pivotsPositive bSize s X tb td G sources seed V outside
      l a b c ha hb hab hs Xp Xm hi hz)

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI
