import Mathlib
import OAI.Analysis.MatrixSigning.Potential.EndpointCandidates
import OAI.Analysis.MatrixSigning.Optimization.NearestEndpoint
import OAI.Analysis.MatrixSigning.Realization.FilterRealization
import OAI.Analysis.MatrixSigning.Realization.FaceArrayRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

abbrev vectorUpdateCode := prodCode vectorCode (prodCode natCode ratCode)
def updateData (p : List ℚ×(ℕ×ℚ)) : List ℚ :=
  (List.range p.1.length).map (fun j => if j=p.2.1 then p.2.2 else p.1.getD j 0)
def updateVector : Realizes vectorUpdateCode vectorCode updateData :=
  let p := first vectorUpdateCode natCode
  let xs := p.then (first vectorCode (prodCode natCode ratCode))
  let args := p.then (second vectorCode (prodCode natCode ratCode))
  let i := args.then (first natCode ratCode)
  let t := args.then (second natCode ratCode)
  let j := second vectorUpdateCode natCode
  let old := (j.both xs).then (getD ratCode 0)
  let one := ((j.both i).then natEq).ite t old
  (((identity vectorUpdateCode).both ((first vectorCode (prodCode natCode ratCode)).then (lengthList ratCode))).then one.tabulate).congr (by
    intro p;simp only [updateData,id_eq,decide_eq_true_eq])
lemma update_data {n : ℕ} (x : Fin n → ℚ) (i : Fin n) (t : ℚ) :
    updateData (List.ofFn x,(i.val,t))=List.ofFn (Function.update x i t) := by
  rw [updateData,List.length_ofFn,range_map_fin]
  congr 1
  funext j
  rw [getD_ofFn]
  by_cases h : j=i
  · subst j;simp
  · have hv : j.val≠i.val := fun hh => h (Fin.ext hh)
    simp [h,hv,Function.update]

def endpointEntry : Realizes (prodCode vectorCode natCode) (listCode vectorCode)
    (fun p => [updateData (p.1,(p.2,-1)),updateData (p.1,(p.2,1))]) :=
  let x := first vectorCode natCode
  let i := second vectorCode natCode
  let point (t : ℚ) := ((x.both (i.both (constant (prodCode vectorCode natCode) ratCode t))).then updateVector)
  ((point (-1)).both ((point 1).then (singleton vectorCode))).then (consList vectorCode)
def endpointData (xs : List ℚ) : List (List ℚ) :=
  (List.range xs.length).flatMap (fun i => [updateData (xs,(i,-1)),updateData (xs,(i,1))])
def endpointCandidates : Realizes vectorCode (listCode vectorCode) endpointData :=
  ((((identity vectorCode).both ((lengthList ratCode).then range)).then endpointEntry.mapCtx).then (joinList vectorCode)).congr
    (fun _ => rfl)
lemma endpoint_data {n : ℕ} (x : Fin n → ℚ) :
    endpointData (List.ofFn x)=(Difference.endpointCandidates x).map List.ofFn := by
  unfold endpointData Difference.endpointCandidates
  rw [List.length_ofFn,range_finRange,List.flatMap_map,List.map_flatMap]
  apply congrArg (List.flatMap · (List.finRange n))
  funext i
  simp only [update_data,List.map_cons,List.map_nil]

def freezeScalarData (sigma t : ℚ) : ℚ :=
  if 1 - |t| ≤ sigma then RationalFace.nearestEndpoint t else t
lemma nearestEndpoint_idem (t : ℚ) : RationalFace.nearestEndpoint (RationalFace.nearestEndpoint t)=RationalFace.nearestEndpoint t := by
  unfold RationalFace.nearestEndpoint
  split_ifs <;> norm_num at *
lemma freezeScalar_idem (sigma t : ℚ) : freezeScalarData sigma (freezeScalarData sigma t)=freezeScalarData sigma t := by
  unfold freezeScalarData
  split_ifs <;> simp_all only [nearestEndpoint_idem]

def freezeScalar : Realizes (prodCode ratCode ratCode) ratCode (fun p => freezeScalarData p.1 p.2) :=
  let sigma := first ratCode ratCode
  let t := second ratCode ratCode
  let c (q : ℚ) := constant (prodCode ratCode ratCode) ratCode q
  let endpoint := (((c 0).le t).ite (c 1) (c (-1)))
  ((((c 1).sub t.abs).le sigma).ite endpoint t).congr (by
    intro p;simp only [freezeScalarData,RationalFace.nearestEndpoint,decide_eq_true_eq])
def freezeVector := freezeScalar.mapCtx
lemma freezeOne_at {n : ℕ} (sigma : ℚ) (x : Fin n → ℚ) (i j : Fin n) :
    RationalFace.freezeOne sigma x j i=if i=j then freezeScalarData sigma (x i) else x i := by
  by_cases hij : i=j
  · subst i
    unfold RationalFace.freezeOne freezeScalarData
    split_ifs <;> simp_all
  · unfold RationalFace.freezeOne
    split_ifs <;> simp [hij]
lemma freezeList_at {n : ℕ} (sigma : ℚ) (xs : List (Fin n)) (x : Fin n → ℚ) (i : Fin n) :
    RationalFace.freezeList sigma x xs i=if i∈xs then freezeScalarData sigma (x i) else x i := by
  induction xs generalizing x with
  | nil => simp [RationalFace.freezeList]
  | cons j js ih =>
    rw [RationalFace.freezeList,ih,freezeOne_at]
    by_cases hij : i=j
    · subst j
      simp [freezeScalar_idem]
    · simp only [hij,ite_false,List.mem_cons,false_or]
lemma freezeVector_data {n : ℕ} (sigma : ℚ) (x : Fin n → ℚ) :
    (List.ofFn x).map (freezeScalarData sigma)=List.ofFn (RationalFace.freezeAll sigma x) := by
  rw [List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply,RationalFace.freezeAll,freezeList_at,List.mem_finRange,ite_true]

end CurrentKS.Realization

end

end OAI
