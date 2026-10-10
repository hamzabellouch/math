import Mathlib
import OAI.Analysis.MatrixSigning.Realization.RawMatrixMachine

namespace OAI

section

namespace CurrentKS.DenseInputArrays
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def fields (x : Input) (i : Fin x.N) : List RationalEntry :=
  (List.ofFn fun j : Fin x.d =>
    (List.ofFn fun k : Fin x.d => x.entries i j k).flatMap
      (fun z => [z.1,z.2])).flatten

def records (x : Input) : List (List RationalEntry) := List.ofFn (fields x)

def canonical (x : Input) : List Bool := RawMatrixMachine.canonicalTape (records x)

lemma fields_length (x : Input) (i : Fin x.N) : (fields x i).length=2*x.d*x.d := by
  simp [fields,List.length_flatten,List.length_flatMap,List.map_ofFn,List.sum_ofFn]
  ring

lemma flatten_fields (rs : List (List RationalEntry)) :
    RawRationalArrayMachine.rawTape rs.flatten =
      (rs.map RawRationalArrayMachine.rawTape).flatten := by
  induction rs with
  | nil => rfl
  | cons a as ih => simp [RawRationalArrayMachine.rawTape,List.flatMap_append] at *;exact ih

lemma complex_fields (zs : List RationalComplex) :
    RawRationalArrayMachine.rawTape (zs.flatMap (fun z => [z.1,z.2])) =
      zs.flatMap encodeComplex := by
  simp only [RawRationalArrayMachine.rawTape,List.flatMap_assoc,List.flatMap_cons,
    List.flatMap_nil,List.append_nil]
  rfl

lemma fields_raw (x : Input) (i : Fin x.N) :
    true :: RawRationalArrayMachine.rawTape (fields x i)=x.encodeMatrix i := by
  simp only [fields,Input.encodeMatrix,flatten_fields,List.map_ofFn,Function.comp_def,complex_fields]

lemma records_length (x : Input) : (records x).length=x.N := by simp [records]

lemma records_field_length (x : Input) (a : List RationalEntry) (ha : a∈records x) :
    a.length=2*x.d*x.d := by
  simp only [records,List.mem_ofFn] at ha
  obtain ⟨i,rfl⟩ := ha
  exact fields_length x i

lemma records_raw (x : Input) : RawMatrixMachine.rawTape (records x)=DenseInputMachine.denseTape x := by
  simp [RawMatrixMachine.rawTape,records,DenseInputMachine.denseTape,
    List.flatMap_def,List.map_ofFn,Function.comp_def,fields_raw]

lemma field_raw_le_dense (x : Input) (a : List RationalEntry) (ha : a∈records x) :
    (RawRationalArrayMachine.rawTape a).length≤(DenseInputMachine.denseTape x).length := by
  rw [←records_raw]
  have hs : (true :: RawRationalArrayMachine.rawTape a).Sublist
      (RawMatrixMachine.rawTape (records x)) := by
    simpa [RawMatrixMachine.rawTape] using (List.singleton_sublist.mpr ha).flatMap
      (fun a => true :: RawRationalArrayMachine.rawTape a)
  have hh := hs.length_le
  simp only [List.length_cons] at hh
  omega

lemma field_raw_le_input (x : Input) (a : List RationalEntry) (ha : a∈records x) :
    (RawRationalArrayMachine.rawTape a).length≤x.length :=
  (field_raw_le_dense x a ha).trans (DenseInputMachine.denseTape_length_le x)

lemma canonical_length_le_raw (rs : List (List RationalEntry)) :
    (RawMatrixMachine.canonicalTape rs).length≤8*(RawMatrixMachine.rawTape rs).length := by
  induction rs with
  | nil => simp [RawMatrixMachine.canonicalTape,RawMatrixMachine.rawTape]
  | cons a as ih =>
    have h := RawRationalArrayMachine.canonical_length_le a
    simp only [RawMatrixMachine.canonicalTape,RawMatrixMachine.rawTape,
      List.flatMap_cons,List.length_append,List.length_cons,KS.W01.length_frame] at *
    omega

lemma canonical_length_le_input (x : Input) : (canonical x).length≤8*x.length := by
  have h := canonical_length_le_raw (records x)
  rw [records_raw] at h
  exact h.trans (Nat.mul_le_mul_left 8 (DenseInputMachine.denseTape_length_le x))

lemma count_le_length (x : Input) : x.N≤x.length := by
  have h : (records x).length≤(RawMatrixMachine.rawTape (records x)).length := by
    generalize records x = rs
    induction rs with
    | nil => simp [RawMatrixMachine.rawTape]
    | cons a as ih => simp only [RawMatrixMachine.rawTape,List.flatMap_cons,
        List.length_append,List.length_cons] at *; omega
  rw [records_length,records_raw] at h
  exact h.trans (DenseInputMachine.denseTape_length_le x)

lemma dimension_sq_le_length (x : Input) (hN : x.N≠0) : 2*x.d*x.d≤x.length := by
  have hi : fields x ⟨0,Nat.pos_of_ne_zero hN⟩ ∈ records x := by simp [records]
  have h := RawRationalArrayMachine.count_le_raw (fields x ⟨0,Nat.pos_of_ne_zero hN⟩)
  rw [fields_length] at h
  exact h.trans (field_raw_le_input x _ hi)

lemma dimension_le_length (x : Input) (hN : x.N≠0) : x.d≤x.length := by
  have h := dimension_sq_le_length x hN
  nlinarith [Nat.zero_le (x.d-1),Nat.mul_self_le_mul_self (show 0≤x.d by omega)]

theorem canonical_scan_spec (x : Input) :
    RunSpec RawMatrixMachine.program
      (RawMatrixMachine.state (DenseInputMachine.denseTape x) [] [] []
        (RawMatrixMachine.unary (2*x.d*x.d)))
      (RawMatrixMachine.state [] (canonical x) [] [] (RawMatrixMachine.unary (2*x.d*x.d)))
      ((x.N*(600*(x.length+1)^4+1)+1)+(canonical x).length+1) := by
  have h := RawMatrixMachine.program_spec (records x) (2*x.d*x.d) x.length
    (records_field_length x) (field_raw_le_input x)
  simpa only [records_raw,records_length,canonical] using h

lemma canonical_scan_polynomial (x : Input) :
    (x.N*(600*(x.length+1)^4+1)+1)+(canonical x).length+1≤610*(x.length+1)^5 := by
  have hN := count_le_length x
  have hC := canonical_length_le_input x
  have hmul : x.N*(600*(x.length+1)^4+1)≤x.length*(600*(x.length+1)^4+1) :=
    Nat.mul_le_mul_right _ hN
  nlinarith [Nat.zero_le (x.length^2),Nat.zero_le (x.length^3),
    Nat.zero_le (x.length^4),Nat.zero_le (x.length^5)]

end CurrentKS.DenseInputArrays

end

end OAI
