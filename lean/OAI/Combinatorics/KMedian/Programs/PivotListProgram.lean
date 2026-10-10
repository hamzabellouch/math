import Mathlib
import OAI.Combinatorics.KMedian.Compression.ComputedPivot
import OAI.Combinatorics.KMedian.Binary.BinaryListIndex
import OAI.Combinatorics.KMedian.Binary.BinaryListZip
import OAI.Combinatorics.KMedian.Compression.GaussianListOperations
import OAI.Combinatorics.KMedian.Compression.IntegerListProgram
import OAI.Combinatorics.KMedian.Optimization.LPMinimumSelection

namespace OAI


                                        
section
namespace MetricKMedian.IntegerLaw.ListPivot
open Binary Binary.PolyProgram Function Finset
abbrev Row := Binary.IntegerList.Row
abbrev er := Binary.IntegerList.er
abbrev Entry := ℤ × ℤ
abbrev ee := encodePair Signed.encode Signed.encode
abbrev ees := encodeList ee

def ratio (e : Entry) : ℚ := (e.1:ℚ)/(e.2:ℚ)
def least (es : List Entry) : ℚ := LPBinary.minimum (((es.filter (fun e => decide (0<e.2))).map ratio))
def pivot (es : List Entry) : ℕ := es.findIdx (fun e => decide (0<e.2 ∧ ratio e=least es))

theorem least_ofFn {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) :
    least (List.ofFn (fun i => (μ.numerator i,z i)))=leastRatio μ z h := by
  apply LPBinary.minimum_eq_finset
  intro q
  simp only [List.mem_map,List.mem_filter,List.mem_ofFn,decide_eq_true_eq,mem_image,positiveSet,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨e,⟨⟨i,rfl⟩,hi⟩,rfl⟩
    exact ⟨i,hi,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨(μ.numerator i,z i),⟨⟨i,rfl⟩,hi⟩,rfl⟩

theorem pivot_ofFn {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) :
    pivot (List.ofFn (fun i => (μ.numerator i,z i)))=(computedPivot μ z h).val := by
  unfold pivot
  rw [least_ofFn μ z h]
  let p := computedPivot μ z h
  apply (List.findIdx_eq (by simpa only [List.length_ofFn] using p.isLt)).mpr
  constructor
  · have hp := mem_filter.mp (min'_mem (pivotSet μ z h) (pivotSet_nonempty μ z h))
    simpa only [List.getElem_ofFn,decide_eq_true_eq,ratio,IntegerLaw.ratio] using ⟨(mem_filter.mp hp.1).2,hp.2⟩
  · intro j hj
    simp only [List.getElem_ofFn,decide_eq_false_iff_not]
    intro hp
    have hm : p ≤ (⟨j,Nat.lt_trans hj p.isLt⟩ : Fin n) := min'_le (pivotSet μ z h) _
      (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hp.1⟩,hp.2⟩)
    exact (not_le_of_gt hj) hm

noncomputable def ratioProgram : PolyProgram ee Ratio.encode ratio :=
  ((((fst Signed.encode Signed.encode).comp ratOfInt).fanout ((snd Signed.encode Signed.encode).comp ratOfInt)).comp ratDiv).congr _ (fun _ => rfl)
noncomputable def positiveProgram : PolyProgram ee encodeBool (fun e : Entry => decide (0<e.2)) :=
  (((constant ee Signed.encode 0).fanout (snd Signed.encode Signed.encode)).comp intLT).congr _ (fun _ => rfl)
noncomputable def leastProgram : PolyProgram ees Ratio.encode least :=
  ((((positiveProgram.listFilter (0,0)).comp (ratioProgram.listMap (0,0))).comp LPBinary.Program.minimumProgram)).congr _ (fun _ => rfl)
noncomputable def pivotProgram : PolyProgram ees Nat.bits pivot := by
  let m := fst Ratio.encode ee
  let e := snd Ratio.encode ee
  let eq := ((e.comp ratioProgram).fanout m).comp ratEQ
  let test := ((e.comp positiveProgram).fanout eq).comp boolAnd
  let tests := (leastProgram.fanout (identity ees)).comp (test.listMapWith (0,0) false)
  exact (tests.comp (listFindIdx (identity encodeBool) false)).congr _ (fun es => by
    simp only [Function.comp_def, List.findIdx_map, id_eq, pivot, Bool.decide_and])

abbrev LawData := ℤ × Row
abbrev el := encodePair Signed.encode er

def update (μ : LawData) (z : Row) : LawData :=
  let es := μ.2.zip z
  let p := pivot es
  let b := es[p]?.getD (0,0)
  (μ.1*b.2,es.map (fun e => e.1*b.2-b.1*e.2))

theorem update_ofFn {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) (hzsum : ∑ i, z i=0) :
    update (μ.denominator,List.ofFn μ.numerator) (List.ofFn z)=
      let ν := eliminateAt μ z (computedPivot μ z h) (computedPivot_spec μ z h).1 (computedPivot_spec μ z h).2 hzsum
      (ν.denominator,List.ofFn ν.numerator) := by
  simp only [update,Gaussian.ListOperation.zip_ofFn,pivot_ofFn μ z h,Gaussian.ListOperation.get_ofFn,List.map_ofFn,
    Function.comp_def,eliminateAt,Vector.getElem_ofFn]

noncomputable def updateProgram : PolyProgram (encodePair el er) el (fun x : LawData × Row => update x.1 x.2) := by
  let μ := fst el er
  let num := μ.comp (snd Signed.encode er)
  let z := snd el er
  let es := (num.fanout z).comp (listZip Signed.encode Signed.encode 0 0)
  let p := es.comp pivotProgram
  let b := (es.fanout p).comp (listGetD ee (0,0))
  let g := fst ee ee
  let e := snd ee ee
  let m1 := ((e.comp (fst Signed.encode Signed.encode)).fanout (g.comp (snd Signed.encode Signed.encode))).comp intMul
  let m2 := ((g.comp (fst Signed.encode Signed.encode)).fanout (e.comp (snd Signed.encode Signed.encode))).comp intMul
  let coord := (m1.fanout m2).comp intSub
  let nums := (b.fanout es).comp (coord.listMapWith (0,0) 0)
  let den := ((μ.comp (fst Signed.encode er)).fanout (b.comp (snd Signed.encode Signed.encode))).comp intMul
  exact (den.fanout nums).congr _ (fun _ => rfl)

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
