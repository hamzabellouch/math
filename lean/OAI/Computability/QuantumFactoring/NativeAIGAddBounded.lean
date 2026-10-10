import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGAdd
import OAI.Computability.QuantumFactoring.NativeAIGBounds

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def RefsBound (B : ℕ) (xs : List Ref) : Prop := xs.length≤B ∧ ∀a∈xs,a.1≤B
lemma RefsBound.mono {A B : ℕ} {xs : List Ref} (h : A≤B) (hx : RefsBound A xs) : RefsBound B xs :=
  ⟨hx.1.trans h,fun a ha=>(hx.2 a ha).trans h⟩
lemma RefsBound.get {B : ℕ} {xs : List Ref} (hx : RefsBound B xs) (i : ℕ) :
    ((xs.drop i).headD (0,false)).1≤B := by
  cases he : (xs.drop i).head? with
  | none=>simp only [List.headD_eq_head?_getD,he,Option.getD_none];omega
  | some a=>
    rw [List.headD_eq_head?_getD,he,Option.getD_some]
    exact hx.2 a (List.mem_of_mem_drop (List.mem_of_head? he))
lemma RefsBound.push {B : ℕ} {xs : List Ref} (hx : RefsBound B xs) (a : Ref) (ha : a.1≤B+13) :
    RefsBound (B+13) (xs++[a]) := by
  refine ⟨?_,?_⟩
  · simp only [List.length_append,List.length_singleton];have:=hx.1;omega
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (hx.2 r hr).trans (by omega)
    · have he : r=a:=List.mem_singleton.mp hr
      simpa only [he] using ha
lemma refsCode_bound {B : ℕ} {xs : List Ref} (h : RefsBound B xs) :
    (listCode refCode xs).length≤10*(B+1)^2 := by
  have hh:=listCode_length_bound refCode xs (2*B+2) (fun a ha=>refCode_length_bound a (h.2 a ha))
  have hm : xs.length*(2*(2*B+2)+2)≤B*(2*(2*B+2)+2) := Nat.mul_le_mul_right _ h.1
  nlinarith
structure AddData where
  budget : ℕ
  graph : Graph
  lhs : List Ref
  rhs : List Ref
  curr : ℕ
  cin : Ref
  output : List Ref

def AddOK (s : AddData) : Prop :=
  Bounded s.budget s.graph ∧ RefsBound s.budget s.lhs ∧ RefsBound s.budget s.rhs ∧
  s.curr≤ s.budget ∧ s.cin.1≤ s.budget ∧ RefsBound s.budget s.output
abbrev AddState := {s : AddData // AddOK s}
def addStepData (s : AddData) : AddData :=
  let r:=full s.graph ((s.lhs.drop s.curr).headD (0,false)) ((s.rhs.drop s.curr).headD (0,false)) s.cin
  ⟨s.budget+13,r.1,s.lhs,s.rhs,s.curr+1,r.2.2,s.output++[r.2.1]⟩
lemma addStep_ok (s : AddState) : AddOK (addStepData s.val) := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have hh:=full_bound hg _ _ s.val.cin (hl.get s.val.curr) (hr.get s.val.curr) hci
  unfold AddOK
  dsimp only [addStepData]
  refine ⟨hh.1.mono (by omega),hl.mono (by omega),hr.mono (by omega),by omega,
    hh.2.2.trans (by omega),?_⟩
  exact ho.push _ (hh.2.1.trans (by omega))
def addStep (s : AddState) : AddState := ⟨addStepData s.val,addStep_ok s⟩
def addDataView (s : AddData) := (s.budget,(s.graph,(s.lhs,(s.rhs,(s.curr,(s.cin,s.output))))))
def addDataCode (s : AddData) : List Bool :=
  prodCode unaryCode (prodCode graphCode (prodCode (listCode refCode)
    (prodCode (listCode refCode) (prodCode Nat.bits (prodCode refCode (listCode refCode)))))) (addDataView s)
def addStateCode (s : AddState) : List Bool := addDataCode s.val
lemma addStateCode_bound (s : AddState) : (addStateCode s).length≤300*(s.val.budget+1)^2 := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have h1:=graphCode_length_bound hg
  have h2:=refsCode_bound hl
  have h3:=refsCode_bound hr
  have h4:=(nat_bits_length_bound s.val.curr).trans hc
  have h5:=refCode_length_bound s.val.cin hci
  have h6:=refsCode_bound ho
  simp only [refCode,prodCode,pairBits_length] at h5
  simp only [addStateCode,addDataCode,addDataView,prodCode,pairBits_length,unaryCode,List.length_replicate]
  nlinarith
lemma budget_le_code (s : AddState) : s.val.budget≤(addStateCode s).length := by
  simp only [addStateCode,addDataCode,addDataView,prodCode,pairBits_length,unaryCode,List.length_replicate]
  omega
lemma addStep_budget (s : AddState) : (addStep s).val.budget=s.val.budget+13 := rfl
lemma addStep_iterate_budget (s : AddState) (k : ℕ) :
    ((addStep^[k]) s).val.budget=s.val.budget+13*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,addStep_budget];omega
lemma addStep_iterate_loop (s : AddState) (k : ℕ) :
    (((addStep^[k]) s).val.graph,((addStep^[k]) s).val.output)=
      addLoop k s.val.graph s.val.lhs s.val.rhs s.val.curr s.val.cin s.val.output := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>
    rw [Function.iterate_succ_apply,ih]
    rfl
end ExactQuantumFactoring.NativeAIG

end



end OAI
