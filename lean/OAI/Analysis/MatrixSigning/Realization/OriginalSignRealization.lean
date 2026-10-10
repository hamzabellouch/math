import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Signing
import OAI.Analysis.MatrixSigning.Realization.VarianceRealization
import OAI.Analysis.MatrixSigning.Realization.OriginalFieldsRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def recordTraceData (p : ℕ×List ℚ) : ℚ :=
  ((List.range p.1).map (fun i => recordEntryData false ((p,i),i))).sum

def recordTrace : Realizes recordCode ratCode recordTraceData :=
  let p := first recordCode natCode
  let i := second recordCode natCode
  let entry := ((p.both i).both i).then (recordEntry false)
  ((((identity recordCode).both (first natCode vectorCode)).then entry.tabulate).then sumRationals)
lemma recordTrace_data (x : Input) (i : Fin x.N) :
    recordTraceData (x.d,fieldValues x i)=RationalInput.trace x i := by
  unfold recordTraceData
  rw [range_map_fin,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  have h := fieldValues_get x i j j (0 : Fin 2)
  simpa [recordEntryData] using h

def originalTrace : Realizes (finFamilyCode originalCode Input.N) ratCode
    (fun p => RationalInput.trace p.1 p.2) :=
  (originalRecord.then recordTrace).congr (fun p => recordTrace_data p.1 p.2)
def originalTraces : Realizes originalCode vectorCode (fun x => List.ofFn (RationalInput.trace x)) :=
  originalTrace.tabulateFin originalN

def originalScale : Realizes originalCode ratCode RationalInput.scale :=
  (originalTraces.then l1Rationals).congr (by intro x;simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn];rfl)
def originalOrientation : Realizes (finFamilyCode originalCode Input.N) ratCode
    (fun p => RationalInput.orientation p.1 p.2) :=
  (((constant _ ratCode 0).le originalTrace).ite (constant _ ratCode 1) (constant _ ratCode (-1))).congr
    (by intro p;simp only [RationalInput.orientation,decide_eq_true_eq])

def nonzeroIndicesData (xs : List ℚ) : List ℕ :=
  (List.range xs.length).filter (fun i => decide (xs.getD i 0≠0))
def nonzeroIndices : Realizes vectorCode indicesCode nonzeroIndicesData :=
  let xs := first vectorCode natCode
  let i := second vectorCode natCode
  let val := (i.both xs).then (getD ratCode 0)
  let iszero := val.eq (constant _ ratCode 0)
  let nonzero := iszero.ite (constant _ boolCode false) (constant _ boolCode true)
  (((identity vectorCode).both ((lengthList ratCode).then range)).then nonzero.filterCtx).congr
    (by intro xs;simp only [nonzeroIndicesData];congr 1;funext i;by_cases h : xs.getD i 0=0 <;> simp_all)
lemma nonzeroIndices_data (x : Input) :
    nonzeroIndicesData (List.ofFn (RationalInput.trace x))=List.ofFn (fun j => (RationalInput.index x j).val) := by
  have h : nonzeroIndicesData (List.ofFn (RationalInput.trace x))=(RationalInput.indices x).map Fin.val := by
    unfold nonzeroIndicesData RationalInput.indices
    rw [List.length_ofFn,range_finRange,List.filter_map]
    congr 1
    apply List.filter_congr
    intro i hi
    rw [Function.comp_apply,getD_ofFn]
  rw [h]
  change _=List.ofFn (Fin.val ∘ (RationalInput.indices x).get)
  rw [←List.map_ofFn,List.ofFn_get]

def originalIndices : Realizes originalCode indicesCode
    (fun x => List.ofFn (fun j => (RationalInput.index x j).val)) :=
  (originalTraces.then nonzeroIndices).congr nonzeroIndices_data
abbrev originalCount (x : Input) := (RationalInput.indices x).length

def originalCountRealizes : Realizes originalCode natCode originalCount :=
  (originalIndices.then (lengthList natCode)).congr (fun _ => List.length_ofFn)

def originalIndex : Realizes (finFamilyCode originalCode originalCount) (finFamilyCode originalCode Input.N)
    (fun p => ⟨p.1,RationalInput.index p.1 p.2⟩) :=
  let x : Realizes (finFamilyCode originalCode originalCount) originalCode (fun p => p.1) := familyFirst
  let i : Realizes (finFamilyCode originalCode originalCount) natCode (fun p => p.2.val) := familyIndex
  (x.both ((i.both (x.then originalIndices)).then (getD natCode 0))).changeOutput
    (finFamilyCode originalCode Input.N) (fun p => ⟨p.1,RationalInput.index p.1 p.2⟩)
    (by intro p;rw [getD_ofFn];rfl)

def originalNormalizedMatrix : Realizes (finFamilyCode originalCode originalCount) matrixCode
    (fun p => matrixData (RationalSDP.realFinDecode p.1.d (RationalInput.normalizedCoordinates p.1 p.2))) :=
  let x : Realizes (finFamilyCode originalCode originalCount) originalCode (fun p => p.1) := familyFirst
  let scale := (constant _ ratCode 1).div (x.then originalScale)
  let orient := originalIndex.then originalOrientation
  let coord := originalIndex.then (originalRecord.then recordCoordinates)
  let normalized := ((scale.mul orient).both coord).then matrixScale
  (((x.then originalD).both normalized).then realDecode).congr (by
    intro p
    erw [recordCoordinates_data,matrixScale_data]
    change realDecodeData (p.1.d,matrixData (fun j k => (1/RationalInput.scale p.1*RationalInput.orientation p.1 (RationalInput.index p.1 p.2))*RationalInput.coordinates p.1 (RationalInput.index p.1 p.2) (j,k)))=_
    have he : (fun j k => (1/RationalInput.scale p.1*RationalInput.orientation p.1 (RationalInput.index p.1 p.2))*RationalInput.coordinates p.1 (RationalInput.index p.1 p.2) (j,k))=
        (fun j k => RationalInput.normalizedCoordinates p.1 p.2 (j,k)) := by
      funext j k
      simp only [RationalInput.normalizedCoordinates,Pi.smul_apply,smul_eq_mul,one_div,mul_assoc]
    rw [he]
    exact realDecode_data _)

def originalFace (x : Input) : FaceParams :=
  ⟨x.d,originalCount x,RationalInput.normalizedCoordinates x,fun _ => 0,0,0⟩

def originalFaceRealizes : Realizes originalCode faceCode originalFace :=
  let atoms := originalNormalizedMatrix.tabulateFin originalCountRealizes
  let zeros := ((constant originalCode ratCode 0).both originalCountRealizes).then (replicateList ratCode)
  (originalD.both (atoms.both (zeros.both (constant originalCode (prodCode ratCode ratCode) (0,0))))).changeOutput
    faceCode originalFace (by intro x;simp only [←List.ofFn_const];rfl)

def originalNormalizedSigns : Realizes originalCode vectorCode
    (fun x => List.ofFn (RationalFace.normalizedRun (RationalInput.normalizedCoordinates x))) :=
  originalFaceRealizes.then normalizedRun

def originalExtendedSigns : Realizes originalCode vectorCode
    (fun x => List.ofFn (RationalFace.extend (RationalInput.index x) (fun _ => 1)
      (RationalFace.normalizedRun (RationalInput.normalizedCoordinates x)))) :=
  let ones := ((constant originalCode ratCode 1).both originalN).then (replicateList ratCode)
  ((originalIndices.both (ones.both originalNormalizedSigns)).then extendVector).congr (by
    intro x
    rw [←List.ofFn_const,extendData_data])

def originalOutputBit : Realizes (finFamilyCode originalCode Input.N) boolCode
    (fun p => decide (RationalInput.orientation p.1 p.2*
      RationalFace.extend (RationalInput.index p.1) (fun _ => 1)
        (RationalFace.normalizedRun (RationalInput.normalizedCoordinates p.1)) p.2=1)) :=
  let x : Realizes (finFamilyCode originalCode Input.N) originalCode (fun p => p.1) := familyFirst
  let i : Realizes (finFamilyCode originalCode Input.N) natCode (fun p => p.2.val) := familyIndex
  let val := (i.both (x.then originalExtendedSigns)).then (getD ratCode 0)
  ((originalOrientation.mul val).eq (constant _ ratCode 1)).congr (by intro p;rw [getD_ofFn])

def originalSigningFramed : Realizes originalCode (listCode boolCode) RationalInput.signing :=
  let alltrue := ((constant originalCode boolCode true).both originalN).then (replicateList boolCode)
  let nontrivial := originalOutputBit.tabulateFin originalN
  (((originalCountRealizes.then natIsZero).ite alltrue nontrivial)).congr
    (by intro x;simp only [RationalInput.signing,decide_eq_true_eq])

end CurrentKS.Realization

end OAI
