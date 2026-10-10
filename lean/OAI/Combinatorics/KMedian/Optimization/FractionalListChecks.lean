import Mathlib
import OAI.Combinatorics.KMedian.Optimization.ApproximateLPSelection
import OAI.Combinatorics.KMedian.Optimization.ApproximationListProgram
import OAI.Combinatorics.KMedian.Binary.BinaryListExtras

namespace OAI


                                            
section
namespace MetricKMedian.LPBinary.Repair
open Binary Binary.PolyProgram Function Finset

def bounded (q : ℚ) : Bool := decide (0 ≤ q ∧ q ≤ 1)
def dominated (xs ys : Row) : Bool := (xs.zip ys).all (fun p => decide (0 ≤ p.1 ∧ p.1 ≤ p.2))
def valid (a : Output) (k : ℕ) : Bool :=
  a.1.all bounded && a.2.all (fun xs => dominated xs a.1) &&
    a.2.all (fun xs => decide (xs.sum=1)) && decide (a.1.sum ≤ (k:ℚ)+1)
def dot (xs ds : Row) : ℚ := ((xs.zip ds).map (fun p => p.1*p.2)).sum
def value (a : Output) (ds : Rows) : ℚ := ((a.2.zip ds).map (fun p => dot p.1 p.2)).sum

theorem all_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (p : α → Bool) :
    (List.ofFn f).all p=true ↔ ∀ i, p (f i)=true := by
  simp only [List.all_eq_true,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]

theorem valid_encodeData {n m : ℕ} (a : TruncatedLP.FractionalData n m) (k : ℕ) :
    valid (encodeData a) k=decide (a.Valid k) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [valid,encodeData,Bool.and_eq_true,all_ofFn,bounded,dominated,Gaussian.ListOperation.zip_ofFn,
    decide_eq_true_eq,List.sum_ofFn,TruncatedLP.FractionalData.Valid,ProjectedSubgradient.point]
  tauto

theorem value_encodeData {n m : ℕ} (a : TruncatedLP.FractionalData n m) (d : Fin m → Fin n → ℚ) :
    value (encodeData a) (List.ofFn (fun j => List.ofFn (d j)))=a.value d := by
  simp only [value,encodeData,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def,dot,List.sum_ofFn,
    TruncatedLP.FractionalData.value,ProjectedSubgradient.point]

noncomputable def boundedProgram : PolyProgram Ratio.encode encodeBool bounded := by
  let lo := ((constant Ratio.encode Ratio.encode 0).fanout (identity Ratio.encode)).comp ratLE
  let hi := ((identity Ratio.encode).fanout (constant Ratio.encode Ratio.encode 1)).comp ratLE
  exact ((lo.fanout hi).comp boolAnd).congr _ (fun q => by simp only [Function.comp_apply,id_eq,bounded,Bool.decide_and])
noncomputable def dominatedProgram : PolyProgram (encodePair er er) encodeBool (fun x : Row × Row => dominated x.1 x.2) := by
  let lo := ((constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 0).fanout (fst Ratio.encode Ratio.encode)).comp ratLE
  let test := (lo.fanout ratLE).comp boolAnd
  exact ((listZip Ratio.encode Ratio.encode 0 0).comp (test.listAll (0,0))).congr _ (fun _ => by simp only [Function.comp_def,dominated,Bool.decide_and])
noncomputable def validProgram : PolyProgram (encodePair eo Nat.bits) encodeBool (fun x : Output × ℕ => valid x.1 x.2) := by
  let a := fst eo Nat.bits
  let ys := a.comp (fst er ers)
  let xs := a.comp (snd er ers)
  let k := ((snd eo Nat.bits).comp ratOfNat).fanout (constant (encodePair eo Nat.bits) Ratio.encode 1) |>.comp ratAdd
  let yb := ys.comp (boundedProgram.listAll 0)
  let rowDom := (exchange er er).comp dominatedProgram
  let dom := (ys.fanout xs).comp (rowDom.listAllWith [])
  let one := ((ratSum.fanout (constant er Ratio.encode 1)).comp ratEQ).listAll []
  let sums := xs.comp one
  let cap := ((ys.comp ratSum).fanout k).comp ratLE
  exact (((((yb.fanout dom).comp boolAnd).fanout sums).comp boolAnd).fanout cap |>.comp boolAnd).congr _ (fun _ => rfl)
noncomputable def dotProgram : PolyProgram (encodePair er er) Ratio.encode (fun x : Row × Row => dot x.1 x.2) :=
  ((listZipWith Ratio.encode Ratio.encode 0 0 ratMul).comp ratSum).congr _ (fun _ => rfl)
noncomputable def valueProgram : PolyProgram (encodePair eo ers) Ratio.encode (fun x : Output × Rows => value x.1 x.2) := by
  let xs := (fst eo ers).comp (snd er ers)
  let ds := snd eo ers
  exact (((xs.fanout ds).comp (listZipWith er er [] [] dotProgram)).comp ratSum).congr _ (fun _ => rfl)
end MetricKMedian.LPBinary.Repair
end

end OAI
