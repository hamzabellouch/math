import Mathlib
import OAI.Combinatorics.KMedian.Geometry.BoundFreeCompression
import OAI.Combinatorics.KMedian.Compression.AffineListCompiler
import OAI.Combinatorics.KMedian.Programs.PivotListProgram
import OAI.Combinatorics.KMedian.Binary.BinaryGuard

namespace OAI


                                           
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset
abbrev Row := Binary.IntegerList.Row
abbrev Rows := Binary.IntegerList.Rows
abbrev er := Binary.IntegerList.er
abbrev em := Binary.IntegerList.em
abbrev es := Gaussian.ListOperation.eslots
abbrev LawData := ListPivot.LawData
abbrev el := ListPivot.el
abbrev Data := List Unit × (LawData × Rows)
abbrev ed := encodePair es (encodePair el em)

structure Input where
  n : ℕ
  d : ℕ
  μ : IntegerLaw (Fin n)
  v : Fin n → Fin d → ℤ

def Input.lawData (I : Input) : LawData := (I.μ.denominator,List.ofFn I.μ.numerator)
def Input.features (I : Input) : Rows := List.ofFn (fun i => List.ofFn (I.v i))
def Input.raw (I : Input) : Data := (List.replicate I.d (),(I.lawData,I.features))
abbrev Input.encode (I : Input) := ed I.raw

def Input.large (I : Input) : Prop := I.d+1 < I.μ.support.card
instance : DecidablePred Input.large := fun _ => inferInstanceAs (Decidable (_<_))
def Input.nextLaw (I : Input) : IntegerLaw (Fin I.n) :=
  if h : I.large then compressionStepAuto I.μ I.v h else I.μ

def Input.step (I : Input) : Input := {I with μ := I.nextLaw}
def Input.affine (I : Input) (h : I.large) : ListOperation.Input := ⟨I.n,I.d,I.μ,I.v,h⟩

noncomputable def rawProgram : PolyProgram Input.encode ed Input.raw :=
  (identity ed).recode Input.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def lawProgram : PolyProgram Input.encode el Input.lawData :=
  ((rawProgram.comp (snd es (encodePair el em))).comp (fst el em)).congr _ (fun _ => rfl)
noncomputable def featuresProgram : PolyProgram Input.encode em Input.features :=
  ((rawProgram.comp (snd es (encodePair el em))).comp (snd el em)).congr _ (fun _ => rfl)
noncomputable def dimProgram : PolyProgram Input.encode es (fun I => List.replicate I.d ()) :=
  (rawProgram.comp (fst es (encodePair el em))).congr _ (fun _ => rfl)

noncomputable def largeProgram : PolyProgram Input.encode encodeBool (fun I => decide I.large) := by
  let nums := lawProgram.comp (snd Signed.encode er)
  let nonz := (((identity Signed.encode).fanout (constant Signed.encode Signed.encode 0)).comp intEQ).comp boolNot
  let size := (nums.comp (nonz.listFilter 0)).comp (listLength Signed.encode 0)
  let dim := ((dimProgram.comp (listLength Gaussian.ListOperation.eu ())).fanout (constant Input.encode Nat.bits 1)).comp natAdd
  exact ((dim.fanout size).comp natLT).congr _ (fun I => by
    simp only [Function.comp_apply,Input.large,Input.lawData,List.length_replicate]
    congr 1
    congr 1
    change ((List.ofFn I.μ.numerator).filter (fun z => !decide (z=0))).length=I.μ.support.card
    have he : (List.ofFn I.μ.numerator).filter (fun z => !decide (z=0))=
        List.ofFn (fun j : Fin I.μ.support.card => I.μ.numerator ((I.μ.support.orderIsoOfFin rfl) j).val) := by
      simp only [← decide_not]
      rw [List.ofFn_eq_map,List.filter_map]
      exact EncodingLists.map_filter_enum _ (fun i => I.μ.numerator i≠0)
    rw [he,List.length_ofFn])

def dummy : Input := ⟨3,0,⟨3,by norm_num,(fun _ => 1),by intros; norm_num,by norm_num⟩,fun _ i => Fin.elim0 i⟩
theorem dummy_large : dummy.large := by
  change 1 < (Finset.univ.filter (fun _ : Fin 3 => (1:ℤ) ≠ 0)).card
  norm_num

noncomputable def productiveProgram : PolyProgram (fun I : {I : Input // I.large} => I.val.encode) el
    (fun I => (I.val.step).lawData) := by
  let a := dimProgram.fanout ((lawProgram.comp (snd Signed.encode er)).fanout featuresProgram)
  let A : PolyProgram (fun I : {I : Input // I.large} => I.val.encode) ListOperation.Input.encode
      (fun I => I.val.affine I.property) :=
    a.recode (fun I : {I : Input // I.large} => I.val) (fun _ => rfl) (fun _ => rfl)
  let K := A.comp ListOperation.affineKernelProgram
  let M := lawProgram.recode (fun I : {I : Input // I.large} => I.val) (fun _ => rfl) (fun _ => rfl)
  exact ((M.fanout K).comp ListPivot.updateProgram).congr _ (fun I => by
    unfold Input.step Input.lawData Input.nextLaw
    rw [dite_eq_left I.property]
    obtain ⟨L,hL⟩ := exists_feature_bound I.val.v
    have hz := computedAffineKernel_spec I.val.μ I.val.v L hL I.property
    exact ListPivot.update_ofFn I.val.μ _ (positiveSet_nonempty _ hz.2.1 hz.1) hz.2.1)

noncomputable def nextLawProgram : PolyProgram Input.encode el (fun I => (I.step).lawData) := by
  let safe := checkedProgram Input.large largeProgram ⟨dummy,dummy_large⟩
  let work := safe.comp productiveProgram
  exact (ite largeProgram lawProgram work).congr _ (fun I => by
    by_cases h : I.large
    · simp only [Function.comp_apply, h,decide_true,ite_true,checked,dite_eq_left]
    · simp only [Function.comp_apply, h,decide_false,Bool.false_eq_true,ite_false]
      simp [Input.step,Input.lawData,Input.nextLaw,h])

noncomputable def stepProgram : PolyProgram Input.encode Input.encode Input.step :=
  ((dimProgram.fanout (nextLawProgram.fanout featuresProgram))).recode id (fun _ => rfl) (fun _ => rfl)

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
