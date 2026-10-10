import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeNumericLadder
import OAI.Combinatorics.MatchingCount.Tapes.TreeErasurePrimitives

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered ExecutableLadder

attribute [local instance] Transport.prodOrder Transport.sumOrder
variable {I : Type} [Fintype I] [LinearOrder I] [Inhabited I]
local instance : Inhabited (Replica.Update I) := ⟨Sum.inr default⟩

def typedGuide (x : Context×(I×I)) : Bool := guide (x.1,(index x.2.1,index x.2.2))
def typedPair (x : LocalPairInput Context I (Finset ℕ) Bits) : Finset ℕ×Finset ℕ :=
  pairDraw ((x.1.1,(index x.1.2.1,index x.1.2.2)),x.2)
def typedRefresh (x : LocalRefreshInput Context I Bits) : Finset ℕ := refresh ((x.1.1,index x.1.2),x.2)
def typedGuideRealizer : Realizer (typedGuide (I:=I)) := guideRealizer.recode
  (fun x : Context×(I×I)=>(x.1,(index x.2.1,index x.2.2))) _ (fun _=>rfl) (fun _=>rfl)
def typedPairRealizer : Realizer (typedPair (I:=I)) := pairRealizer.recode
  (fun x : LocalPairInput Context I (Finset ℕ) Bits=>((x.1.1,(index x.1.2.1,index x.1.2.2)),x.2)) _ (fun _=>rfl) (fun _=>rfl)
def typedRefreshRealizer : Realizer (typedRefresh (I:=I)) := refreshRealizer.recode
  (fun x : LocalRefreshInput Context I Bits=>((x.1.1,index x.1.2),x.2)) _ (fun _=>rfl) (fun _=>rfl)
abbrev TypedInput (I : Type) := List (List Bool×Bits)×(RunSetup Context I ℕ×StateTable I (Finset ℕ))
def typedExecute (x : TypedInput I) : RunSetup Context I ℕ×StateTable I (Finset ℕ) :=
  x.1.foldl (fun z b=>runStep typedGuide typedPair typedRefresh (b,z)) x.2
def typedExecuteRealizer : Realizer (typedExecute (I:=I)) :=
  fold (runStepRealizer typedGuideRealizer typedPairRealizer typedRefreshRealizer Numbered.equal Numbered.lessEqual natEqual)
lemma polynomial_typedExecute : PolynomialTime (typedExecuteRealizer (I:=I)) :=
  polynomial_scanRun (polynomial_recode _ _ _ _ polynomial_guide)
    (polynomial_recode _ _ _ _ polynomial_pair) (polynomial_recode _ _ _ _ polynomial_refresh)
    Numbered.polynomial_equal Numbered.polynomial_lessEqual polynomial_natEqual

lemma inl_program_zero (hz : index (default : I)=0) :
    (TreeTyped.inl (A:=I×I) (B:=I)).program=(TreeTyped.inl (A:=ℕ×ℕ) (B:=ℕ)).program := by
  simp only [TreeTyped.inl,Realizer.recode,pair]
  rw [constant_program (default : I) (default : ℕ) (C:=I×I) (D:=ℕ×ℕ) (by change TreeData.nat (index (default : I))=TreeData.nat 0; rw [hz])]
  rfl
lemma inr_program_zero (hz : index (default : I)=0) :
    (TreeTyped.inr (A:=I×I) (B:=I)).program=(TreeTyped.inr (A:=ℕ×ℕ) (B:=ℕ)).program := by
  simp only [TreeTyped.inr,Realizer.recode,pair]
  rw [constant_program (default : I×I) (default : ℕ×ℕ) (C:=I) (D:=ℕ) (by
    change TreeData.Data.cons (TreeData.nat (index (default : I))) (TreeData.nat (index (default : I)))=
      TreeData.Data.cons (TreeData.nat 0) (TreeData.nat 0)
    rw [hz])]
  rfl
lemma lookup_program_zero (d : Finset ℕ) (hz : index (default : I)=0) :
    (lookupRealizer (I:=I) d Numbered.equal).program=(lookupRealizer (I:=ℕ) d natEqual).program := by
  dsimp only [lookupRealizer,filterWith,mapWith,mapStepRealizer,TreeTyped.map,TreeTyped.filter,
    Realizer.congr,composition,pair,choose,fold, Numbered.equal,Realizer.recode]
  simp only [program_constant,encode_list_nil]
  rw [head_program ((default : I),d) ((default : ℕ),d) (by
    change TreeData.Data.cons (TreeData.nat (index (default : I))) (encode d)=
      TreeData.Data.cons (TreeData.nat 0) (encode d)
    rw [hz])]
  rfl
lemma normalize_program_zero (hz : index (default : I)=0) :
    (normalizeStateRealizer (I:=I) (E:=ℕ) Numbered.equal natEqual).program=
      (normalizeStateRealizer (I:=ℕ) (E:=ℕ) natEqual natEqual).program := by
  dsimp only [normalizeStateRealizer,mapWith,mapStepRealizer,Realizer.congr,composition,pair,fold]
  simp only [program_constant,encode_list_nil]
  rw [lookup_program_zero ∅ hz]
  rfl
lemma none_encode_zero (hz : index (default : I)=0) :
    encode (none : Option (Replica.Update I))=encode (none : Option (Replica.Update ℕ)) := by
  have hd : encode (default : I)=encode (0 : ℕ) := by
    change TreeData.nat (index (default : I))=TreeData.nat 0; rw [hz]
  change encode (false,(false,(((default : I),(default : I)),(default : I))))=
    encode (false,(false,(((0 : ℕ),(0 : ℕ)),(0 : ℕ))))
  simp only [encode_prod,hd]
lemma choice_program_zero (hz : index (default : I)=0) :
    (scanChoiceRealizer (I:=I) typedGuideRealizer Numbered.equal Numbered.lessEqual).program=
      (scanChoiceRealizer guideRealizer natEqual leNat).program := by
  dsimp only [scanChoiceRealizer,updateSetRealizer,updateListRealizer, TreeTyped.map,
    Realizer.congr,composition,pair,fold]
  rw [inl_program_zero hz,inr_program_zero hz]
  rw [constant_program (none : Option (Replica.Update I)) (none : Option (Replica.Update ℕ))
    (none_encode_zero hz) (C:=ScanSetup Context I) (D:=ScanSetup Context ℕ)]
  simp only [program_constant,encode_list_nil]
  rfl
lemma local_program_zero (hz : index (default : I)=0) :
    (localSamplerRealizer (I:=I) typedPairRealizer typedRefreshRealizer Numbered.equal).program=
      (localSamplerRealizer pairRealizer refreshRealizer natEqual).program := by
  dsimp only [localSamplerRealizer,optionCases,sumCases,localPairRealizer,localRefreshRealizer,
    Realizer.congr,Realizer.recode,composition,pair,choose]
  rw [lookup_program_zero (default : Finset ℕ) hz]
  rfl
lemma scan_program_zero (hz : index (default : I)=0) :
    (scanRealizer (I:=I) typedGuideRealizer typedPairRealizer typedRefreshRealizer Numbered.equal Numbered.lessEqual).program=
      (scanRealizer guideRealizer pairRealizer refreshRealizer natEqual leNat).program := by
  dsimp only [scanRealizer,Realizer.congr,composition,pair]
  rw [choice_program_zero hz,local_program_zero hz,draw_program
    (none : Option (Replica.Update I)) (none : Option (Replica.Update ℕ)) (none_encode_zero hz)]
  rfl
lemma typedExecute_program (hz : index (default : I)=0) :
    (typedExecuteRealizer (I:=I)).program=executeRealizer.program := by
  dsimp only [typedExecuteRealizer,executeRealizer,fold,runStepRealizer,Realizer.congr,composition,pair]
  rw [scan_program_zero hz,normalize_program_zero hz]
  rfl
end MatchingFPRAS.NumericLadder

end OAI
