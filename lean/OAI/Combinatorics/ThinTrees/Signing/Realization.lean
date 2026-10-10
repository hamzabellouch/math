import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialOriginalSigning
import OAI.Combinatorics.ThinTrees.Signing.FormSigning
import OAI.Combinatorics.ThinTrees.Signing.GramRealization

namespace OAI

/-! Signing realization. -/

section

namespace AlgorithmicThinTrees.Signing.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix

structure Frame where
  d : ℕ
  m : ℕ
  v : Fin m → Fin d → ℚ

abbrev frameDataCode := prodCode natCode matrixCode
def Frame.data (a : Frame) := (a.d,matrixData a.v)
def frameCode (a : Frame) : Word := frameDataCode a.data
abbrev frameView : Realizes frameCode frameDataCode Frame.data :=
  (identity frameDataCode).reindex frameCode Frame.data (fun _ => rfl)
private instance poly_frameView : PolyTime frameView := by
  unfold frameView
  apply poly_reindex

abbrev frameDim := frameView.then (first natCode matrixCode)
abbrev frameRows := frameView.then (second natCode matrixCode)
private instance poly_frameDim : PolyTime frameDim := by
  unfold frameDim
  apply poly_then

private instance poly_frameRows : PolyTime frameRows := by
  unfold frameRows
  apply poly_then

def complexField : Realizes ratCode vectorCode (fun q => [q,0]) :=
  ((identity ratCode).both (constant ratCode vectorCode [0])).then (consList ratCode)
instance poly_complexField : PolyTime complexField := by unfold complexField;infer_instance

def outerFields : Realizes vectorCode vectorCode
    (fun xs : List ℚ => (xs.map (fun q =>
      (xs.map (fun r => [q*r,0])).flatten)).flatten) :=
  ((Normalization.Stack.outer.then complexField.map.map).then (joinList vectorCode)).then
    (joinList ratCode) |>.congr (by
      intro xs
      simp only [List.map_map,Function.comp_def,List.flatten_flatten])
instance poly_outerFields : PolyTime outerFields := by unfold outerFields;infer_instance

lemma outerFields_data {d m : ℕ} (v : Fin m → Fin d → ℚ) (e : Fin m) :
    ((List.ofFn (v e)).map (fun q =>
      ((List.ofFn (v e)).map (fun r => [q*r,0])).flatten)).flatten=
      fieldValues (RationalSigning.input v) e := by
  refine Eq.trans ?_ (fieldValues_eq (RationalSigning.input v) e).symm
  simp only [List.map_ofFn,Function.comp_def,RationalSigning.input,RationalSigning.entry_value]

def signerInput : Realizes frameCode originalCode (fun a => RationalSigning.input a.v) :=
  (frameDim.both (frameRows.then outerFields.map)).changeOutput originalCode
    (fun a => RationalSigning.input a.v) (by
      intro a
      change frameDataCode (a.d,_) = originalDataCode (originalData _)
      congr 1
      change (a.d,_)=(a.d,List.ofFn (fieldValues (RationalSigning.input a.v)))
      apply congrArg (fun xs => (a.d,xs))
      change (matrixData a.v).map _ = _
      change (List.ofFn (fun e => List.ofFn (a.v e))).map _ = _
      rw [List.map_ofFn]
      exact congrArg List.ofFn (funext (outerFields_data a.v)))
instance poly_signerInput : PolyTime signerInput := by
  unfold signerInput
  apply poly_changeOutput

def signs : Realizes frameCode (listCode boolCode)
    (fun a => CurrentKS.RationalInput.signing (RationalSigning.input a.v)) :=
  signerInput.then originalSigningFramed

lemma runsPoly_signs {ι : Type*} {L : ι → ℕ} (a : ι → Frame)
    (ha : IsPoly L (fun i => (frameCode (a i)).length)) : RunsPoly L signs a := by
  have hi := RunsPoly.of_poly signerInput a ha
  exact hi.then (runsPoly_originalSigningFramed _ hi.output
    (fun i => RationalSigning.input_admissible (a i).v))

structure FormFrame where
  form : MatrixObject
  m : ℕ
  v : Fin m → Fin form.1 → ℚ

abbrev formDataCode := prodCode matrixObjectCode matrixCode
def FormFrame.data (a : FormFrame) := (a.form,matrixData a.v)
def formCode (a : FormFrame) : Word := formDataCode a.data
abbrev formView : Realizes formCode formDataCode FormFrame.data :=
  (identity formDataCode).reindex formCode FormFrame.data (fun _ => rfl)
private instance poly_formView : PolyTime formView := by
  unfold formView
  apply poly_reindex

abbrev formMatrix := formView.then (first matrixObjectCode matrixCode)
abbrev formRows := formView.then (second matrixObjectCode matrixCode)

lemma factorColumns_data (a : MatrixObject) :
    (RationalGram.factorColumns a.1 a.2).map List.ofFn=
      matrixData (RationalGram.factorMatrix a.2)ᵀ := by
  change (RationalGram.factorColumns a.1 a.2).map List.ofFn=
      List.ofFn (fun i => List.ofFn ((RationalGram.factorColumns a.1 a.2).get i))
  have he : List.map List.ofFn (List.ofFn (RationalGram.factorColumns a.1 a.2).get)=
      List.ofFn (List.ofFn ∘ (RationalGram.factorColumns a.1 a.2).get) := List.map_ofFn
  simpa only [List.ofFn_get,Function.comp_def] using he

def factorRows : Realizes matrixObjectCode matrixCode
    (fun a => matrixData (GramWhitening.rationalFactor a.2)ᵀ) :=
  (rationalInverseProgram.then gramColumnsProgram).congr
    (fun a => factorColumns_data ⟨a.1,RationalInverse.inverse a.1 a.2⟩)

lemma runsPoly_factorRows {ι : Type*} {L : ι → ℕ} (a : ι → MatrixObject)
    (ha : IsPoly L (fun i => (matrixObjectCode (a i)).length))
    (hA : ∀i,((a i).2.map (fun q : ℚ => (q:ℝ))).PosDef) :
    RunsPoly L factorRows a := by
  have hi := runsPoly_rationalInverse a ha hA
  unfold factorRows
  apply RunsPoly.congr
  apply hi.then
  apply runsPoly_gramColumns _ hi.output
  intro i
  rw [RationalInverse.inverse_eq_of_cast _ (hA i),GramWhitening.cast_inverse]
  exact (hA i).inv.posSemidef

def FormFrame.whiten (a : FormFrame) : Frame :=
  ⟨(RationalGram.factorColumns a.form.1 (RationalInverse.inverse a.form.1 a.form.2)).length,
    a.m,FormSigning.whiten a.form.2 a.v⟩

def whiten : Realizes formCode frameCode FormFrame.whiten :=
  let R := formMatrix.then factorRows
  let cols := (R.both formRows).then matVec.mapCtx
  ((R.then (lengthList vectorCode)).both cols).changeOutput frameCode FormFrame.whiten (by
    intro a
    change frameDataCode (_,_) = frameDataCode (Frame.data _)
    congr 1
    dsimp only [FormFrame.data,Frame.data,FormFrame.whiten]
    refine Prod.ext (List.length_ofFn) ?_
    change List.map _ (List.ofFn (fun e => List.ofFn (a.v e)))=matrixData _
    rw [List.map_ofFn]
    simp only [Function.comp_def,matVec_data]
    rfl)

lemma runsPoly_whiten {ι : Type*} {L : ι → ℕ} (a : ι → FormFrame)
    (ha : IsPoly L (fun i => (formCode (a i)).length))
    (hA : ∀i,((a i).form.2.map (fun q : ℚ => (q:ℝ))).PosDef) :
    RunsPoly L whiten a := by
  have : PolyTime formMatrix := by
    unfold formMatrix
    apply poly_then
  have : PolyTime formRows := by
    unfold formRows
    apply poly_then
  have hf := RunsPoly.of_poly formMatrix a ha
  have hr := hf.then (runsPoly_factorRows _ hf.output hA)
  have hc := (hr.both (RunsPoly.of_poly formRows a ha)).then_poly matVec.mapCtx
  unfold whiten
  apply RunsPoly.changeOutput
  exact (hr.then_poly (lengthList vectorCode)).both hc

structure FramePair where
  a : ℕ
  b : ℕ
  m : ℕ
  u : Fin m → Fin a → ℚ
  v : Fin m → Fin b → ℚ

def FramePair.left (a : FramePair) : Frame := ⟨a.a,a.m,a.u⟩
def FramePair.right (a : FramePair) : Frame := ⟨a.b,a.m,a.v⟩
def FramePair.stack (a : FramePair) : Frame :=
  ⟨a.a+a.b,a.m,fun e => StackedSigning.stack (a.u e) (a.v e)⟩
def pairCode (a : FramePair) : Word := prodCode frameCode frameCode (a.left,a.right)
abbrev pairView : Realizes pairCode (prodCode frameCode frameCode)
    (fun a => (a.left,a.right)) :=
  (identity (prodCode frameCode frameCode)).reindex pairCode
    (fun a => (a.left,a.right)) (fun _ => rfl)
private instance poly_pairView : PolyTime pairView := by
  unfold pairView
  apply poly_reindex

abbrev pairLeft := pairView.then (first frameCode frameCode)
abbrev pairRight := pairView.then (second frameCode frameCode)

lemma stack_data {a b : ℕ} (u : Fin a → ℚ) (v : Fin b → ℚ) :
    List.ofFn u++List.ofFn v=List.ofFn (StackedSigning.stack u v) := by
  rw [List.ofFn_add]
  change List.ofFn u++List.ofFn v=
    (List.ofFn (fun i => StackedSigning.stack u v (Fin.castAdd b i)))++
      (List.ofFn (fun i => StackedSigning.stack u v (Fin.natAdd a i)))
  simp only [StackedSigning.stack_left,StackedSigning.stack_right]

def stack : Realizes pairCode frameCode FramePair.stack :=
  let dims := ((pairLeft.then frameDim).both (pairRight.then frameDim)).then natAdd
  let rows := ((pairLeft.then frameRows).both (pairRight.then frameRows)).then
    ((appendList ratCode).zipWith [] [])
  (dims.both rows).changeOutput frameCode FramePair.stack (by
    intro a
    change frameDataCode (_,_) = frameDataCode _
    congr 1
    change (a.a+a.b,zipDefault (fun p : List ℚ × List ℚ => p.1 ++ p.2) [] []
      (List.ofFn (fun i : Fin a.m => List.ofFn (a.u i)),
        List.ofFn (fun i : Fin a.m => List.ofFn (a.v i)))) =
      (a.a+a.b,List.ofFn (fun i : Fin a.m => List.ofFn (StackedSigning.stack (a.u i) (a.v i))))
    rw [zipDefault_ofFn]
    simp only [stack_data])
instance poly_stack : PolyTime stack := by
  have : PolyTime pairLeft := by unfold pairLeft; apply poly_then
  have : PolyTime pairRight := by unfold pairRight; apply poly_then
  unfold stack
  apply poly_changeOutput

structure FormPair where
  a : MatrixObject
  b : MatrixObject
  m : ℕ
  u : Fin m → Fin a.1 → ℚ
  v : Fin m → Fin b.1 → ℚ

def FormPair.left (p : FormPair) : FormFrame := ⟨p.a,p.m,p.u⟩
def FormPair.right (p : FormPair) : FormFrame := ⟨p.b,p.m,p.v⟩
def FormPair.whiten (p : FormPair) : FramePair :=
  ⟨p.left.whiten.d,p.right.whiten.d,p.m,p.left.whiten.v,p.right.whiten.v⟩
def formsCode (p : FormPair) : Word := prodCode formCode formCode (p.left,p.right)
abbrev formsView : Realizes formsCode (prodCode formCode formCode)
    (fun p => (p.left,p.right)) :=
  (identity (prodCode formCode formCode)).reindex formsCode
    (fun p => (p.left,p.right)) (fun _ => rfl)
private instance poly_formsView : PolyTime formsView := by
  unfold formsView
  apply poly_reindex

abbrev formsLeft := formsView.then (first formCode formCode)
abbrev formsRight := formsView.then (second formCode formCode)

def whitenPair : Realizes formsCode pairCode FormPair.whiten :=
  ((formsLeft.then whiten).both (formsRight.then whiten)).changeOutput
    pairCode FormPair.whiten (fun _ => rfl)

def simultaneousSigns : Realizes formsCode (listCode boolCode)
    (fun p => CurrentKS.RationalInput.signing (RationalSigning.input
      (fun e => StackedSigning.stack (FormSigning.whiten p.a.2 p.u e)
        (FormSigning.whiten p.b.2 p.v e)))) :=
  whitenPair.then (stack.then signs)

lemma runsPoly_simultaneousSigns {ι : Type*} {L : ι → ℕ} (a : ι → FormPair)
    (ha : IsPoly L (fun i => (formsCode (a i)).length))
    (hA : ∀i,((a i).a.2.map (fun q : ℚ => (q:ℝ))).PosDef)
    (hB : ∀i,((a i).b.2.map (fun q : ℚ => (q:ℝ))).PosDef) :
    RunsPoly L simultaneousSigns a := by
  have : PolyTime formsLeft := by
    unfold formsLeft
    apply poly_then
  have : PolyTime formsRight := by
    unfold formsRight
    apply poly_then
  have hu := RunsPoly.of_poly formsLeft a ha
  have hv := RunsPoly.of_poly formsRight a ha
  have hw : RunsPoly L whitenPair a := by
    unfold whitenPair
    apply RunsPoly.changeOutput
    exact (hu.then (runsPoly_whiten _ hu.output hA)).both
      (hv.then (runsPoly_whiten _ hv.output hB))
  have hs := hw.then_poly stack
  exact hw.then ((RunsPoly.of_poly stack _ hw.output).then (runsPoly_signs _ hs.output))

end AlgorithmicThinTrees.Signing.Stack
end

end OAI
