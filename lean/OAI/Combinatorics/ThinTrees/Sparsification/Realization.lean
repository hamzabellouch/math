import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Realization
import OAI.Combinatorics.ThinTrees.Continuation.BitBound
import OAI.Combinatorics.ThinTrees.Sparsification.Step

namespace OAI

/-! Sparsification realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

def ratNatFloorBinary : Realizes ratCode binaryNatCode (fun q => ⌊q⌋₊) :=
  ((((constant ratCode ratCode 0).max (identity ratCode)).then ratFloor).then
    ratNumBinary).congr (by
      intro q
      have he : (⌊max 0 q⌋ : ℤ)=(⌊q⌋₊ : ℤ) := by
        by_cases hq : 0 ≤ q
        · rw [max_eq_right hq,Int.natCast_floor_eq_floor hq]
        · rw [max_eq_left (le_of_not_ge hq),Int.floor_zero,Nat.floor_eq_zero.mpr (by linarith)]
          rfl
      change KS.W01.intPayload ⌊max 0 q⌋=⌊q⌋₊
      rw [he,intPayload_natCast])
instance poly_ratNatFloorBinary : PolyTime ratNatFloorBinary := by
  unfold ratNatFloorBinary;infer_instance

lemma runsPoly_binaryToNat {ι : Type*} {L : ι → ℕ} (a : ι → ℕ)
    (ha : IsPoly L (fun i => (binaryNatCode (a i)).length)) (hn : IsPoly L a) :
    RunsPoly L binaryToNat a := by
  refine ⟨ha,?_⟩
  exact (((isPoly_const L 6).mul hn).add ((isPoly_const L 4).mul ha)).add (isPoly_const L 4)

end CurrentKS.Realization

namespace AlgorithmicThinTrees.GraphicHalf.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree Finset
open MetricTests MetricTests.RationalStep Normalization GraphStack
open MetricTests.RationalStep.Stack

structure Problem where
  d : ℕ
  m : ℕ
  r : ℕ
  G : MultiGraph (d+1) m

def Problem.graph (p : Problem) : Graph := ⟨p.d+1,p.m,p.G⟩
def problemCode (p : Problem) : Word := extractionInputCode (p.graph,p.r)
abbrev problemView : Realizes problemCode extractionInputCode (fun p => (p.graph,p.r)) :=
  (identity extractionInputCode).reindex problemCode (fun p => (p.graph,p.r)) (fun _ => rfl)
private instance poly_problemView : PolyTime problemView := by
  unfold problemView
  apply poly_reindex

abbrev problemGraph := problemView.then extractionGraph
abbrev problemCount := problemView.then extractionCount
abbrev problemN := problemGraph.then numVertices
abbrev problemM := problemGraph.then numEdges

private theorem poly_problemM : PolyTime problemM := by
  unfold problemM
  apply poly_then

def problemD : Realizes problemCode natCode Problem.d :=
  (problemN.then natPred).congr (fun _ => rfl)
instance poly_problemD : PolyTime problemD := by unfold problemD; apply poly_congr

def extraction : Realizes problemCode loopCode (fun p => ⟨p.graph,p.r,extractState p.G p.r⟩) :=
  problemView.then extract
instance poly_extraction : PolyTime extraction := by unfold extraction; apply poly_then
abbrev Problem.state (p : Problem) := extractState p.G p.r
abbrev Problem.active (p : Problem) := p.state.active
abbrev Problem.q (p : Problem) := p.state.packingTarget
abbrev Problem.scales (p : Problem) := normalizedScales p.q p.r (graphColumns p.G p.active)

lemma packingTarget_le (p : Problem) : p.q ≤ p.r := by
  have h := (stateAt_quality p.G p.r (scheduleLength p.m p.r)).2
  have hq : p.state.quality ≤ (p.r:ℚ) := by exact_mod_cast h
  exact (Nat.floor_mono (show p.state.quality-1 ≤ (p.r:ℚ) by linarith)).trans_eq (Nat.floor_natCast _)

def targetBinary : Realizes problemCode binaryNatCode Problem.q :=
  (((extraction.then loopQuality).sub (constant problemCode ratCode 1)).then ratNatFloorBinary)
instance poly_targetBinary : PolyTime targetBinary := by unfold targetBinary; apply poly_then

def targetCount : Realizes problemCode natCode Problem.q := targetBinary.then binaryToNat
instance poly_targetCount : PolyTime targetCount := by
  apply PolyTime.mk
  have ht := RunsPoly.of_poly targetBinary id (isPoly_self (fun p => (problemCode p).length))
  have hn : IsPoly (fun p => (problemCode p).length) Problem.r :=
    ((RunsPoly.of_poly problemCount id (isPoly_self (fun p => (problemCode p).length))).output).mono
      (fun p => by simp only [natCode,List.length_replicate];rfl)
  exact (ht.then (runsPoly_binaryToNat _ ht.output (hn.mono packingTarget_le))).cost

abbrev Edge := Σ p : Problem, Fin p.m
abbrev edgeCode := finFamilyCode problemCode Problem.m
abbrev context : Realizes edgeCode problemCode (fun p : Edge => p.1) := familyFirst
abbrev number : Realizes edgeCode natCode (fun p : Edge => p.2.val) := familyIndex

def edgeGraphInput : Realizes edgeCode GraphStack.edgeCode (fun p => ⟨p.1.graph,p.2⟩) :=
  ((context.then problemGraph).both number).changeOutput GraphStack.edgeCode
    (fun p => ⟨p.1.graph,p.2⟩) (fun _ => rfl)
instance poly_edgeGraphInput : PolyTime edgeGraphInput := by unfold edgeGraphInput; apply poly_changeOutput

def edgeActive : Realizes edgeCode boolCode (fun p => decide (p.2 ∈ p.1.active)) :=
  ((constant edgeCode ratCode 0).lt
    ((number.both (context.then extraction |>.then loopCapacity)).then (getD ratCode 0))).congr
      (by
        intro p
        change decide ((0:ℚ) < (List.ofFn p.1.state.capacity).getD p.2.val 0)=_
        simp only [getD_ofFn,Problem.active,State.active,mem_filter,mem_univ,true_and])
instance poly_edgeActive : PolyTime edgeActive := by unfold edgeActive;infer_instance

def fullColumn : Realizes edgeCode vectorCode (fun p => List.ofFn (fullColumns p.1.G p.1.active p.2)) :=
  (edgeActive.ite (edgeGraphInput.then incidence)
    (((constant edgeCode ratCode 0).both (context.then problemN)).then (replicateList ratCode))).congr
      (by
        intro p
        simp only [decide_eq_true_eq]
        split_ifs with h
        · rw [fullColumns,ite_eq_left h];rfl
        · rw [fullColumns,ite_eq_right h]
          change List.replicate (p.1.d+1) (0:ℚ)=List.ofFn (fun _ : Fin (p.1.d+1) => (0:ℚ))
          exact (List.ofFn_const _ (0:ℚ)).symm)
instance poly_fullColumn : PolyTime fullColumn := by unfold fullColumn; apply poly_congr

def fullRows : Realizes problemCode matrixCode (fun p => matrixData (fullColumns p.G p.active)) :=
  fullColumn.tabulateFin problemM
instance poly_fullRows : PolyTime fullRows := by
  unfold fullRows
  exact @poly_tabulateFin _ _ _ _ _ _ _ _ poly_fullColumn poly_problemM

abbrev Coordinate := Σ e : Edge, Fin e.1.d
abbrev coordCode := finFamilyCode edgeCode (fun e : Edge => e.1.d)
abbrev coordEdge : Realizes coordCode edgeCode (fun x : Coordinate => x.1) := familyFirst
abbrev coordIndex : Realizes coordCode natCode (fun x : Coordinate => x.2.val) := familyIndex

lemma graphColumns_drop (p : Problem) (e : Fin p.m) (i : Fin p.d) :
    fullColumns p.G p.active e i.succ=graphColumns p.G p.active e i := by
  simp only [fullColumns,graphColumns,integerColumns,qdiff]
  by_cases h : e ∈ p.active
  · simp only [ite_eq_left h,Pi.sub_apply]
    simp [Pi.single_apply,eq_comm]
  · simp only [ite_eq_right h,Pi.zero_apply,Int.cast_zero]

def reducedEntry : Realizes coordCode ratCode
    (fun x => graphColumns x.1.1.G x.1.1.active x.1.2 x.2) :=
  (((coordIndex.then natSucc).both (coordEdge.then fullColumn)).then (getD ratCode 0)).congr
    (by
      intro x
      change (List.ofFn (fullColumns x.1.1.G x.1.1.active x.1.2)).getD x.2.succ.val 0=_
      rw [getD_ofFn];exact graphColumns_drop _ _ _)
instance poly_reducedEntry : PolyTime reducedEntry := by unfold reducedEntry;infer_instance

def reducedColumn : Realizes edgeCode vectorCode (fun p => List.ofFn (graphColumns p.1.G p.1.active p.2)) :=
  reducedEntry.tabulateFin (context.then problemD)
instance poly_reducedColumn : PolyTime reducedColumn := by unfold reducedColumn;infer_instance

def reducedRows : Realizes problemCode matrixCode (fun p => matrixData (graphColumns p.G p.active)) :=
  reducedColumn.tabulateFin problemM
instance poly_reducedRows : PolyTime reducedRows := by
  unfold reducedRows
  exact @poly_tabulateFin _ _ _ _ _ _ _ _ poly_reducedColumn poly_problemM

def Problem.normalization (p : Problem) : Normalization.Stack.Params :=
  ⟨p.d,p.m,p.q,0,graphColumns p.G p.active⟩

def normalizationParams : Realizes problemCode Normalization.Stack.paramsCode Problem.normalization :=
  (problemD.both (targetCount.both ((constant problemCode ratCode 0).both reducedRows))).changeOutput
    Normalization.Stack.paramsCode Problem.normalization (fun _ => rfl)
instance poly_normalizationParams : PolyTime normalizationParams := by unfold normalizationParams; apply poly_changeOutput

def scales : Realizes problemCode vectorCode (fun p => List.ofFn p.scales) :=
  (normalizationParams.both problemCount).then Normalization.Stack.normalized
instance poly_scales : PolyTime scales := by unfold scales; apply poly_then

def positiveMatrix : Realizes problemCode matrixCode (fun p => matrixData (positiveForm p.state.matrix)) :=
  ((extraction.then loopMatrix).both
    ((problemN.both ((constant problemCode ratCode 1).div (problemN.then natToRat))).then
     constantMatrix)).then matrixAdd |>.congr (by
       intro p
       change matrixAddData (matrixData p.state.matrix,matrixData (Matrix.of (fun (_ _ : Fin (p.d+1)) => 1/((p.d+1:ℕ):ℚ))))=_
       change zipDefault (zipDefault (fun p : ℚ×ℚ => p.1+p.2) 0 0) [] []
         (matrixData p.state.matrix,matrixData (Matrix.of (fun (_ _ : Fin (p.d+1)) => 1/((p.d+1:ℕ):ℚ))))=_
       rw [matrixAdd_data]
       simp only [one_div]
       rfl)
instance poly_positiveMatrix : PolyTime positiveMatrix := by unfold positiveMatrix; apply poly_congr

def secondMatrix : Realizes problemCode matrixCode (fun p => matrixData (scaledForm p.G p.active p.scales)) :=
  let state := (normalizationParams.both scales).changeOutput Normalization.Stack.stateCode
    (fun p : Problem => ⟨p.normalization,p.scales⟩) (fun _ => rfl)
  state.then Normalization.Stack.gram
instance poly_secondMatrix : PolyTime secondMatrix := by
  unfold secondMatrix
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_changeOutput
  · infer_instance

def scaledRows : Realizes problemCode matrixCode (fun p => matrixData (scaledColumns p.G p.active p.scales)) :=
  ((scales.both reducedRows).then (vectorScale.zipWith 0 [])).congr (by
    intro p
    change zipDefault (fun p : ℚ×List ℚ => p.2.map (fun x => p.1*x)) 0 []
      (List.ofFn p.scales,List.ofFn (fun e => List.ofFn (graphColumns p.G p.active e)))=_
    rw [zipDefault_ofFn]
    simp only [List.map_ofFn,Function.comp_def]
    rfl)
instance poly_scaledRows : PolyTime scaledRows := by unfold scaledRows;infer_instance

def Problem.forms (p : Problem) : Signing.Stack.FormPair :=
  ⟨⟨p.d+1,positiveForm p.state.matrix⟩,⟨p.d,scaledForm p.G p.active p.scales⟩,
    p.m,fullColumns p.G p.active,scaledColumns p.G p.active p.scales⟩

def forms : Realizes problemCode Signing.Stack.formsCode Problem.forms :=
  (((problemN.both positiveMatrix).both fullRows).both
    ((problemD.both secondMatrix).both scaledRows)).changeOutput Signing.Stack.formsCode
      Problem.forms (fun _ => rfl)
instance poly_forms : PolyTime forms := by unfold forms; apply poly_changeOutput

abbrev MaskInput := Problem × List Bool
abbrev maskCode := prodCode problemCode (listCode boolCode)
abbrev maskProblem := first problemCode (listCode boolCode)
abbrev maskSigns := second problemCode (listCode boolCode)
abbrev MaskEdge := Σ p : MaskInput, Fin p.1.m
abbrev maskEdgeCode := finFamilyCode maskCode (fun p : MaskInput => p.1.m)
abbrev maskContext : Realizes maskEdgeCode maskCode (fun p : MaskEdge => p.1) := familyFirst
abbrev maskIndex : Realizes maskEdgeCode natCode (fun p : MaskEdge => p.2.val) := familyIndex

def maskEdgeInput : Realizes maskEdgeCode edgeCode (fun p => ⟨p.1.1,p.2⟩) :=
  ((maskContext.then maskProblem).both maskIndex).changeOutput edgeCode
    (fun p => ⟨p.1.1,p.2⟩) (fun _ => rfl)
instance poly_maskEdgeInput : PolyTime maskEdgeInput := by unfold maskEdgeInput; apply poly_changeOutput

def maskBit : Realizes maskEdgeCode boolCode
    (fun p => if p.2 ∈ p.1.1.active then p.1.2.getD p.2.val false else false) :=
  ((maskEdgeInput.then edgeActive).ite
    ((maskIndex.both (maskContext.then maskSigns)).then (getD boolCode false))
    (constant maskEdgeCode boolCode false)).congr (by intro p;simp only [decide_eq_true_eq])
instance poly_maskBit : PolyTime maskBit := by unfold maskBit;infer_instance

def mask : Realizes maskCode (listCode boolCode)
    (fun p => List.ofFn (fun e : Fin p.1.m =>
      if e ∈ p.1.active then p.2.getD e.val false else false)) :=
  maskBit.tabulateFin (maskProblem.then problemM)
instance poly_mask : PolyTime mask := by
  have hm : PolyTime (maskProblem.then problemM) := by
    refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ poly_problemM
    infer_instance
  unfold mask
  exact @poly_tabulateFin _ _ _ _ _ _ _ _ poly_maskBit hm

def signsProgram := forms.then Signing.Stack.simultaneousSigns

def sparsifyProgram : Realizes problemCode (listCode boolCode)
    (fun p => List.ofFn (fun e => decide (e ∈ sparsify p.G p.r))) :=
  (((identity problemCode).both signsProgram).then mask).congr (by
    intro p
    apply congrArg List.ofFn
    funext e
    change (if e ∈ p.active then _ else false)=_
    simp only [sparsify,halfEdges,FormSigning.selected,StackedSigning.selected,
      RationalSigning.selected,mem_inter,mem_filter,mem_univ,true_and]
    by_cases h : e ∈ p.active
    · simp [h,Problem.forms,Problem.active,Problem.state,Problem.scales,Problem.q] at *
    · simp [h] at *)

theorem sparsify_program_polynomial : ∃R : ℕ, 4 ≤ R ∧ ∀{ι : Type} {L : ι → ℕ}
    (a : ι → Problem), IsPoly L (fun i => (problemCode (a i)).length) →
    (∀i, R ≤ (a i).r ∧ 2 ≤ (a i).d+1 ∧ (a i).G.TreePackable univ (a i).r) →
    RunsPoly L sparsifyProgram a := by
  obtain ⟨R,hR,hstep⟩ := shortcut_correct
  refine ⟨R,(by norm_num : 4 ≤ 64^16).trans hR,?_⟩
  intro ι L a ha hp
  have hforms := RunsPoly.of_poly forms a ha
  have hsigns : RunsPoly L signsProgram a := by
    apply hforms.then
    apply Signing.Stack.runsPoly_simultaneousSigns _ hforms.output
    · intro i
      obtain ⟨hX,_,_,_,_,_⟩ := hstep (a i).r (hp i).1 _ _ (a i).G (hp i).2.1 (hp i).2.2
      change ((positiveForm (a i).state.matrix).map (fun q : ℚ => (q:ℝ))).PosDef
      rw [positiveForm_cast]
      have hr : 0 < (a i).r := (by norm_num : 0 < 64^16).trans_le (hR.trans (hp i).1)
      exact regularize_pd (by omega) (domain_positive (a i).G (by omega)
        (packing_connected (a i).G hr (hp i).2.2) hX)
    · intro i
      obtain ⟨hX,hpack,hqpos,hqr,_,_⟩ := hstep (a i).r (hp i).1 _ _ (a i).G (hp i).2.1 (hp i).2.2
      obtain ⟨hs,_,_⟩ := graphic_normalization (a i).G (a i).active hqpos hqr hpack
      change ((scaledForm (a i).G (a i).active (a i).scales).map (fun q : ℚ => (q:ℝ))).PosDef
      rw [scaledForm_cast]
      obtain ⟨F⟩ := graph_containedPacking (a i).G (a i).active hqpos hpack
      exact F.covariance_posDef _ (realWeights_box hs).1
  unfold sparsifyProgram
  apply RunsPoly.congr
  exact ((RunsPoly.of_poly (identity problemCode) a ha).both hsigns).then_poly mask

end AlgorithmicThinTrees.GraphicHalf.Stack
end

end OAI
