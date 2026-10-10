import Mathlib
import OAI.Combinatorics.KMedian.Optimization.LPBinaryStart
import OAI.Combinatorics.KMedian.Geometry.NearestFillingFormula

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset

theorem sum_map_filter_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (p : α → Bool) (v : α → ℚ) :
    (((List.ofFn f).filter p).map v).sum=∑ i ∈ univ.filter (fun i => p (f i)), v (f i) := by
  rw [Finset.sum_filter]
  have he (xs : List α) : ((xs.filter p).map v).sum=(xs.map (fun a => if p a then v a else 0)).sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih]
  rw [he,List.map_ofFn,List.sum_ofFn]
  rfl

namespace Nearest
abbrev Entry := ℕ × (ℚ × ℚ)
abbrev ee := encodePair Nat.bits (encodePair Ratio.encode Ratio.encode)
abbrev ees := encodeList ee

def entries (ys ds : Row) : List Entry :=
  let es := ys.zip ds
  (List.range es.length).zip es

def before (a b : Entry) : Bool := decide (a.2.2 < b.2.2 ∨ a.2.2=b.2.2 ∧ a.1 < b.1)
def prior (es : List Entry) (a : Entry) : ℚ := ((es.filter (fun b => before b a)).map (fun e => e.2.1)).sum
def amount (es : List Entry) (a : Entry) : ℚ := min a.2.1 (max 0 (1-prior es a))
def filling (ys ds : Row) : Row := let es := entries ys ds; es.map (amount es)

theorem entries_ofFn {n : ℕ} (y d : Fin n → ℚ) :
    entries (List.ofFn y) (List.ofFn d)=List.ofFn (fun i => (i.val,(y i,d i))) := by
  simp only [entries,Gaussian.ListOperation.zip_ofFn,List.length_ofFn,range_ofFn]

theorem prior_ofFn {n : ℕ} (y d : Fin n → ℚ) (i : Fin n) :
    prior (List.ofFn (fun j => (j.val,(y j,d j)))) (i.val,(y i,d i))=Preparation.priorMass univ y d i := by
  rw [prior,sum_map_filter_ofFn]
  simp only [before,decide_eq_true_eq,Preparation.priorMass,Preparation.before,Fin.lt_def]

theorem filling_ofFn {n : ℕ} (y d : Fin n → ℚ) (hy : ∀ i, 0 ≤ y i) (hm : 1 ≤ ∑ i, y i) :
    filling (List.ofFn y) (List.ofFn d)=List.ofFn (ProjectedSubgradient.point (Preparation.computedNearest y d hy hm)) := by
  simp only [filling,entries_ofFn,List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply,amount,prior_ofFn,ProjectedSubgradient.point,Preparation.computedNearest_formula]

noncomputable def entriesProgram : PolyProgram (encodePair er er) ees (fun x : Row × Row => entries x.1 x.2) := by
  let ez := encodePair Ratio.encode Ratio.encode
  let zip := listZip Ratio.encode Ratio.encode 0 0
  let ids := listIndices ez (0,0)
  exact (zip.comp ((ids.fanout (identity (encodeList ez))).comp (listZip Nat.bits ez 0 (0,0)))).congr _ (fun _ => rfl)
noncomputable def beforeProgram : PolyProgram (encodePair ee ee) encodeBool (fun x : Entry × Entry => before x.1 x.2) := by
  let a := fst ee ee
  let b := snd ee ee
  let idx := fst Nat.bits (encodePair Ratio.encode Ratio.encode)
  let dist := (snd Nat.bits (encodePair Ratio.encode Ratio.encode)).comp (snd Ratio.encode Ratio.encode)
  let dst := (a.comp dist).fanout (b.comp dist)
  let ilt := ((a.comp idx).fanout (b.comp idx)).comp natLT
  exact (((dst.comp ratLT).fanout (((dst.comp ratEQ).fanout ilt).comp boolAnd)).comp boolOr).congr _ (fun _ => by simp only [Function.comp_apply,before,Bool.decide_or,Bool.decide_and])
noncomputable def priorProgram : PolyProgram (encodePair ees ee) Ratio.encode (fun x : List Entry × Entry => prior x.1 x.2) := by
  let pred := (exchange ee ee).comp beforeProgram
  let filtered := (exchange ees ee).comp (pred.listFilterWith (0,(0,0)) (0,(0,0)))
  let cap := (snd Nat.bits (encodePair Ratio.encode Ratio.encode)).comp (fst Ratio.encode Ratio.encode)
  exact ((filtered.comp (cap.listMap (0,(0,0)))).comp ratSum).congr _ (fun _ => rfl)
noncomputable def amountProgram : PolyProgram (encodePair ees ee) Ratio.encode (fun x : List Entry × Entry => amount x.1 x.2) := by
  let cap := ((snd ees ee).comp (snd Nat.bits (encodePair Ratio.encode Ratio.encode))).comp (fst Ratio.encode Ratio.encode)
  let remain := ((constant (encodePair ees ee) Ratio.encode 1).fanout priorProgram).comp ratSub
  exact ((cap.fanout (remain.comp Program.positivePart)).comp Program.ratMin).congr _ (fun _ => rfl)
noncomputable def fillingProgram : PolyProgram (encodePair er er) er (fun x : Row × Row => filling x.1 x.2) :=
  ((entriesProgram.fanout entriesProgram).comp (amountProgram.listMapWith (0,(0,0)) 0)).congr _ (fun _ => rfl)
end Nearest
end MetricKMedian.LPBinary
end

end OAI
