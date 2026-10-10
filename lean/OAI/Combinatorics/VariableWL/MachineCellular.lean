import OAI.Combinatorics.VariableWL.CellularListing

namespace OAI

namespace VariableWL.CircuitCatalog.Data
 theorem ext_fields {D E : Data}
    (h1 : D.rows=E.rows) (h2 : D.internal=E.internal) (h3 : D.scalars=E.scalars)
    (h4 : D.ands=E.ands) (h5 : D.edges=E.edges) (h6 : D.requests=E.requests)
    (h7 : D.validScalar=E.validScalar) (h8 : D.validAnd=E.validAnd) (h9 : D.validEdge=E.validEdge)
    (h10 : D.validRequest=E.validRequest) (h11 : D.source=E.source) (h12 : D.destination=E.destination)
    (h13 : D.destinationForm=E.destinationForm) (h14 : D.domain=E.domain) (h15 : D.map=E.map)
    (h16 : D.requestGate=E.requestGate) (h17 : D.requestTest=E.requestTest)
    (h18 : D.requestDomain=E.requestDomain) (h19 : D.marked=E.marked) (h20 : D.epsilon=E.epsilon) : D=E := by
  cases D; cases E; congr
end VariableWL.CircuitCatalog.Data
namespace VariableWL.CircuitCatalog.Program.Listing
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
theorem eval_validRequest {n : ℕ} (D : Listing n) (v : Env n) (i : ℕ) : (D.eval v).validRequest i=D.validRequest.bit (cons (List.replicate i true) v) := rfl
theorem eval_source {n : ℕ} (D : Listing n) (v : Env n) (i : ℕ) : (D.eval v).source i=D.source.number (cons (List.replicate i true) v) := rfl
theorem eval_destination {n : ℕ} (D : Listing n) (v : Env n) (i : ℕ) : (D.eval v).destination i=D.destination.number (cons (List.replicate i true) v) := rfl
theorem eval_destinationForm {n : ℕ} (D : Listing n) (v : Env n) (i : ℕ) : (D.eval v).destinationForm i=D.destinationForm.number (cons (List.replicate i true) v) := rfl
theorem eval_domain {n : ℕ} (D : Listing n) (v : Env n) (i j a : ℕ) : (D.eval v).domain i j a=D.domain.bit (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v))) := rfl
theorem eval_map {n : ℕ} (D : Listing n) (v : Env n) (i j a : ℕ) : (D.eval v).map i j a=D.map.number (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v))) := rfl
theorem eval_requestGate {n : ℕ} (D : Listing n) (v : Env n) (i : ℕ) : (D.eval v).requestGate i=D.requestGate.number (cons (List.replicate i true) v) := rfl
theorem eval_requestTest {n : ℕ} (D : Listing n) (v : Env n) (i : ℕ) : (D.eval v).requestTest i=D.requestTest.number (cons (List.replicate i true) v) := rfl
theorem eval_requestDomain {n : ℕ} (D : Listing n) (v : Env n) (i j a : ℕ) : (D.eval v).requestDomain i j a=D.requestDomain.bit (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v))) := rfl
end VariableWL.CircuitCatalog.Program.Listing
namespace VariableWL.CellularCatalog.Data
theorem catalog_validRequest_eq (D : Data) (i : ℕ) : D.catalog.validRequest i=D.validRequest i := rfl
theorem catalog_source_eq (D : Data) (i : ℕ) : D.catalog.source i=D.source i := rfl
theorem catalog_destination_eq (D : Data) (i : ℕ) : D.catalog.destination i=D.destination i := rfl
theorem catalog_destinationForm_eq (D : Data) (i : ℕ) : D.catalog.destinationForm i=D.destinationForm i := rfl
theorem catalog_domain_eq (D : Data) (i j a : ℕ) : D.catalog.domain i j a=D.domain i j a := rfl
theorem catalog_map_eq (D : Data) (i j a : ℕ) : D.catalog.map i j a=D.map i j a := rfl
theorem catalog_requestGate_eq (D : Data) (i : ℕ) : D.catalog.requestGate i=D.requestGate i := rfl
theorem catalog_requestTest_eq (D : Data) (i : ℕ) : D.catalog.requestTest i=D.requestTest i := rfl
theorem catalog_requestDomain_eq (D : Data) (i j a : ℕ) : D.catalog.requestDomain i j a=D.requestDomain i j a := rfl
end VariableWL.CellularCatalog.Data
namespace VariableWL.CellularCatalog.Program.Listing
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
variable {n : ℕ} (D : Listing n)
theorem catalog_validRequest_field : D.catalog.validRequest=D.up.validRequest (Computation.Stack.PolyRecipe.input 0) := rfl
theorem catalog_validRequest_eval (v : Env n) (i : ℕ) : (D.catalog.eval v).validRequest i=(D.eval v).catalog.validRequest i := by
  rw [CircuitCatalog.Program.Listing.eval_validRequest,catalog_validRequest_field,Data.catalog_validRequest_eq,validRequest_bit,eval_up]
  simp only [input_number,cons_zero,List.length_replicate]
theorem catalog_source_field : D.catalog.source=D.up.source (Computation.Stack.PolyRecipe.input 0) := rfl
theorem catalog_source_eval (v : Env n) (i : ℕ) : (D.catalog.eval v).source i=(D.eval v).catalog.source i := by
  rw [CircuitCatalog.Program.Listing.eval_source,catalog_source_field,Data.catalog_source_eq,source_number,eval_up]
  simp only [input_number,cons_zero,List.length_replicate]
theorem catalog_destination_field : D.catalog.destination=D.up.destination (Computation.Stack.PolyRecipe.input 0) := rfl
theorem catalog_destination_eval (v : Env n) (i : ℕ) : (D.catalog.eval v).destination i=(D.eval v).catalog.destination i := by
  rw [CircuitCatalog.Program.Listing.eval_destination,catalog_destination_field,Data.catalog_destination_eq,destination_number,eval_up]
  simp only [input_number,cons_zero,List.length_replicate]
theorem catalog_destinationForm_field : D.catalog.destinationForm=D.up.destinationForm (Computation.Stack.PolyRecipe.input 0) := rfl
theorem catalog_destinationForm_eval (v : Env n) (i : ℕ) : (D.catalog.eval v).destinationForm i=(D.eval v).catalog.destinationForm i := by
  rw [CircuitCatalog.Program.Listing.eval_destinationForm,catalog_destinationForm_field,Data.catalog_destinationForm_eq,destinationForm_number,eval_up]
  simp only [input_number,cons_zero,List.length_replicate]
theorem catalog_domain_field : D.catalog.domain=D.up.up.up.domain (Computation.Stack.PolyRecipe.input 0) (Computation.Stack.PolyRecipe.input 1) (Computation.Stack.PolyRecipe.input 2) := rfl
theorem catalog_domain_eval (v : Env n) (i j a : ℕ) : (D.catalog.eval v).domain i j a=(D.eval v).catalog.domain i j a := by
  rw [CircuitCatalog.Program.Listing.eval_domain,catalog_domain_field,Data.catalog_domain_eq,domain_bit,eval_up,eval_up,eval_up]
  simp only [input_number,cons_zero,cons_one,cons_two,List.length_replicate]
theorem catalog_map_field : D.catalog.map=D.up.up.up.map (Computation.Stack.PolyRecipe.input 0) (Computation.Stack.PolyRecipe.input 1) (Computation.Stack.PolyRecipe.input 2) := rfl
theorem catalog_map_eval (v : Env n) (i j a : ℕ) : (D.catalog.eval v).map i j a=(D.eval v).catalog.map i j a := by
  rw [CircuitCatalog.Program.Listing.eval_map,catalog_map_field,Data.catalog_map_eq,map_number,eval_up,eval_up,eval_up]
  simp only [input_number,cons_zero,cons_one,cons_two,List.length_replicate]
theorem catalog_requestGate_field : D.catalog.requestGate=D.up.requestGate (Computation.Stack.PolyRecipe.input 0) := rfl
theorem catalog_requestGate_eval (v : Env n) (i : ℕ) : (D.catalog.eval v).requestGate i=(D.eval v).catalog.requestGate i := by
  rw [CircuitCatalog.Program.Listing.eval_requestGate,catalog_requestGate_field,Data.catalog_requestGate_eq,requestGate_number,eval_up]
  simp only [input_number,cons_zero,List.length_replicate]
theorem catalog_requestTest_field : D.catalog.requestTest=D.up.requestTest (Computation.Stack.PolyRecipe.input 0) := rfl
theorem catalog_requestTest_eval (v : Env n) (i : ℕ) : (D.catalog.eval v).requestTest i=(D.eval v).catalog.requestTest i := by
  rw [CircuitCatalog.Program.Listing.eval_requestTest,catalog_requestTest_field,Data.catalog_requestTest_eq,requestTest_number,eval_up]
  simp only [input_number,cons_zero,List.length_replicate]
theorem catalog_requestDomain_field : D.catalog.requestDomain=D.up.up.up.requestDomain (Computation.Stack.PolyRecipe.input 0) (Computation.Stack.PolyRecipe.input 1) (Computation.Stack.PolyRecipe.input 2) := rfl
theorem catalog_requestDomain_eval (v : Env n) (i j a : ℕ) : (D.catalog.eval v).requestDomain i j a=(D.eval v).catalog.requestDomain i j a := by
  rw [CircuitCatalog.Program.Listing.eval_requestDomain,catalog_requestDomain_field,Data.catalog_requestDomain_eq,requestDomain_bit,eval_up,eval_up,eval_up]
  simp only [input_number,cons_zero,cons_one,cons_two,List.length_replicate]
 theorem catalog_eval (v : Env n) : D.catalog.eval v=(D.eval v).catalog := by
  apply CircuitCatalog.Data.ext_fields
  · exact add_number D.bits D.bits v
  · rfl
  · rfl
  · change (mul D.triples (numeral 2)).number v=(D.eval v).triples*2
    rw [mul_number,triples_number,numeral_number]
  · change (mul D.triples D.kinds).number v=(D.eval v).triples*(D.eval v).kinds
    rw [mul_number,triples_number,kinds_number]
  · change (add D.initialEnd D.letters).number v=(D.eval v).initialEnd+(D.eval v).letters
    rw [add_number,initialEnd_number]; rfl
  · funext i; rfl
  · funext i; rfl
  · funext i; rfl
  · funext i; exact catalog_validRequest_eval D v i
  · funext i; exact catalog_source_eval D v i
  · funext i; exact catalog_destination_eval D v i
  · funext i; exact catalog_destinationForm_eval D v i
  · funext i j a; exact catalog_domain_eval D v i j a
  · funext i j a; exact catalog_map_eval D v i j a
  · funext i; exact catalog_requestGate_eval D v i
  · funext i; exact catalog_requestTest_eval D v i
  · funext i j a; exact catalog_requestDomain_eval D v i j a
  · rfl
  · rfl
end VariableWL.CellularCatalog.Program.Listing

namespace VariableWL.MachineCellular
open MachineOneHead MachineReduction Descriptor Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
attribute [local instance] Classical.propDecidable
variable (M : Machine)
noncomputable def presentation : Presentation (Letter M) := Presentation.fixed (Letter M)
noncomputable def alpha (first b : Bool) : Alphabet M :=
  (first,Function.update (fun _ : MultiStack.Slot M => none) (0,true) (some (MultiStack.inputSymbol M b)))
noncomputable def headLetter (b : Bool) : Letter M := (alpha M true b,some (oneHead M).start)
noncomputable def tailLetter (b : Bool) : Letter M := (alpha M false b,none)
noncomputable def emptyLetter : Letter M := ((true,fun _=>none),some (oneHead M).start)
noncomputable def initial (v : Word) : List (Alphabet M) := match v with
  | [] => [(true,fun _=>none)]
  | b::bs => alpha M true b :: bs.map (alpha M false)
 theorem input_eq (w : Word) : MachineOneHead.input M w=initial M w.reverse := by
  simp only [MachineOneHead.input,Turing.TM2to1.trInit,←List.map_reverse]
  cases w.reverse with
  | nil => rfl
  | cons b bs =>
    change alpha M true b :: ((bs.map (MultiStack.inputSymbol M)).map (fun a => (false,Function.update (fun _ : MultiStack.Slot M=>none) (0,true) (some a)))) = alpha M true b :: bs.map (alpha M false)
    apply congrArg (List.cons (alpha M true b))
    induction bs with
    | nil => rfl
    | cons a bs ih => exact congrArg (List.cons (alpha M false a)) ih
 theorem initial_length (v : Word) : (initial M v).length=1+(v.length-1) := by
  cases v with
  | nil => rfl
  | cons b bs =>
    change (bs.map (alpha M false)).length+1=1+((bs.length+1)-1)
    rw [List.length_map]; omega
noncomputable def letterInput (v : Word) (j : ℕ) : Letter M :=
  if j=0 then if v.length=0 then emptyLetter M else headLetter M (v.getD j false)
  else tailLetter M (v.getD j false)
 theorem letterInput_eq (v : Word) (j : Fin (initial M v).length) :
    letterInput M v j.val=OneHead.markedInput (oneHead M) (fun i : Fin (initial M v).length => (initial M v)[i]) j := by
  rcases j with ⟨j,hj⟩
  cases v with
  | nil =>
    have he : j=0 := by change j<1 at hj; omega
    subst j
    rfl
  | cons b bs =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j<bs.length := by simpa only [initial,List.length_cons,List.length_map,Nat.succ_lt_succ_iff] using hj
      simp only [letterInput,Nat.succ_ne_zero,ite_false,List.getD_cons_succ,
        List.getD_eq_getElem _ _ hj',tailLetter,OneHead.markedInput,initial,Fin.getElem_fin,List.getElem_cons_succ,List.getElem_map]
 theorem letterInput_original (w : Word) (j : Fin (MachineOneHead.input M w).length) :
    letterInput M w.reverse j.val=OneHead.markedInput (oneHead M) (fun i : Fin (MachineOneHead.input M w).length => (MachineOneHead.input M w)[i]) j := by
  have h:=letterInput_eq M w.reverse ⟨j.val,by rw [←input_eq]; exact j.isLt⟩
  simp only [OneHead.markedInput,Fin.getElem_fin] at h ⊢
  simpa only [input_eq] using h
noncomputable def inputProgram : Expr 2 :=
  choose (eq (input 0) (numeral 0))
    (choose (eq (input 1) (numeral 0)) (numeral ((presentation M).encode (emptyLetter M)))
      (choose (lookup (input 1) (input 0)) (numeral ((presentation M).encode (headLetter M true)))
        (numeral ((presentation M).encode (headLetter M false)))))
    (choose (lookup (input 1) (input 0)) (numeral ((presentation M).encode (tailLetter M true)))
      (numeral ((presentation M).encode (tailLetter M false))))
 theorem cons_one_env1 (a : Word) (v : Env 1) : cons a v (1 : Fin 2)=v 0 := rfl
 theorem inputProgram_number (v : Env 1) (j : ℕ) :
    (inputProgram M).number (cons (List.replicate j true) v)=(presentation M).encode (letterInput M (v 0) j) := by
  simp only [inputProgram,NumericProgram.choose_number,eq_bit,input_number,numeral_number,
    cons_zero,cons_one_env1,List.length_replicate,lookup_bit,Computation.Stack.PolyRecipe.input_value,letterInput,decide_eq_true_eq]
  split_ifs <;> cases hb : (v 0).getD j false <;> simp_all

def fixedPower {n : ℕ} (X : Expr n) : ℕ → Expr n
  | 0 => numeral 1
  | k+1 => mul (fixedPower X k) X
 theorem fixedPower_number {n : ℕ} (X : Expr n) (k : ℕ) (v : Env n) :
    (fixedPower X k).number v=(X.number v)^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [fixedPower,mul_number,ih,pow_succ]
noncomputable def bitProgram (c d : ℕ) : Expr 1 :=
  add (add (numeral (quadraticConstant M+3))
    (mul (numeral 2) (mul (numeral (c+1)) (fixedPower (add (input 0) (numeral 1)) (d+1))))) (numeral 2)
 theorem bitProgram_number (c d : ℕ) (v : Env 1) :
    (bitProgram M c d).number v=addressBits M c d (v 0).length := by
  simp only [bitProgram,add_number,mul_number,numeral_number,fixedPower_number,input_number,
    addressBits,simulationExponent,inputExponent]
noncomputable def ruleCode (a b c : ℕ) : ℕ :=
  if ha : a<(presentation M).bound then if hb : b<(presentation M).bound then if hc : c<(presentation M).bound then
    (presentation M).encode ((oneHead M).rule ((Fintype.equivFin (Letter M)).symm ⟨a,ha⟩)
      ((Fintype.equivFin (Letter M)).symm ⟨b,hb⟩) ((Fintype.equivFin (Letter M)).symm ⟨c,hc⟩)) else 0 else 0 else 0
noncomputable def ruleProgram : Expr 4 :=
  table₃ (presentation M).bound (presentation M).bound (presentation M).bound (ruleCode M) (input 0) (input 1) (input 2)
noncomputable def acceptCode (a : ℕ) : Bool :=
  decide (∃f,(presentation M).encode f=a ∧ (oneHead M).acceptingCell f)
noncomputable def acceptProgram : Expr 2 :=
  choose (lt (input 0) (numeral (presentation M).bound))
    (fixedBool (presentation M).bound (fun i=>acceptCode M i.val) (input 0)) (literal [])
noncomputable def listing (c d : ℕ) (ε : Affine.Bit) : CellularCatalog.Program.Listing 1 where
  bits := bitProgram M c d
  inputLength := add (numeral 1) (sub (input 0) (numeral 1))
  letters := numeral (presentation M).bound
  internal := mul (numeral 4) (add (add (bitProgram M c d) (bitProgram M c d)) (numeral 1))
  rule := ruleProgram M
  input := inputProgram M
  blank := numeral ((presentation M).encode (default,none))
  accepting := acceptProgram M
  marked := numeral 0
  epsilon := numeral ε.val
end VariableWL.MachineCellular

namespace VariableWL.MachineCellular
open MachineOneHead MachineReduction Descriptor Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
attribute [local instance] Classical.propDecidable
variable (M : Machine)
 theorem presentation_encode (a : Letter M) : (presentation M).encode a=(Fintype.equivFin (Letter M) a).val := rfl
 theorem presentation_bound : (presentation M).bound=Fintype.card (Letter M) := rfl
 theorem presentation_valid : (presentation M).valid=fun _=>true := rfl
 theorem ruleCode_encode (a b c : Letter M) :
    ruleCode M ((presentation M).encode a) ((presentation M).encode b) ((presentation M).encode c)=
      (presentation M).encode ((oneHead M).rule a b c) := by
  rw [ruleCode,dite_eq_left ((presentation M).encode_lt a),dite_eq_left ((presentation M).encode_lt b),
    dite_eq_left ((presentation M).encode_lt c)]
  change (presentation M).encode ((oneHead M).rule ((Fintype.equivFin (Letter M)).symm (Fintype.equivFin (Letter M) a)) ((Fintype.equivFin (Letter M)).symm (Fintype.equivFin (Letter M) b)) ((Fintype.equivFin (Letter M)).symm (Fintype.equivFin (Letter M) c)))=_
  simp only [Equiv.symm_apply_apply]
 theorem ruleProgram_number (v : Env 1) (a b c : Letter M) :
    (ruleProgram M).number (cons (List.replicate ((presentation M).encode a) true)
      (cons (List.replicate ((presentation M).encode b) true) (cons (List.replicate ((presentation M).encode c) true) v)))=
    (presentation M).encode ((oneHead M).rule a b c) := by
  rw [ruleProgram,table₃_number]
  simp only [input_number,cons_zero,cons_one,cons_two,List.length_replicate]
  rw [ite_eq_left ⟨(presentation M).encode_lt a,(presentation M).encode_lt b,(presentation M).encode_lt c⟩,
    ruleCode_encode]
 theorem acceptProgram_bit (v : Env 1) (j : ℕ) :
    (acceptProgram M).bit (cons (List.replicate j true) v)=acceptCode M j := by
  rw [acceptProgram,Computation.Stack.PolyRecipe.choose_bit,lt_bit,input_number,cons_zero,List.length_replicate,numeral_number]
  by_cases hj : j<(presentation M).bound
  · rw [ite_eq_left (by simpa using hj),fixedBool_bit _ _ _ _ (by simpa only [input_number,cons_zero,List.length_replicate] using hj)]
    apply congrArg (acceptCode M)
    simp only [input_number,cons_zero,List.length_replicate]
  · rw [ite_eq_right (by simpa using hj)]
    have he : ¬∃f,(presentation M).encode f=j ∧ (oneHead M).acceptingCell f := by
      rintro ⟨f,hf,_⟩
      exact hj (hf ▸ (presentation M).encode_lt f)
    change false=decide _
    exact (decide_eq_false he).symm
 theorem circuit_rule (c d : ℕ) (w : Word) : (MachineReduction.circuit M c d w).rule=(oneHead M).rule := rfl
 theorem circuit_input (c d : ℕ) (w : Word) (j : Fin (MachineOneHead.input M w).length) :
    (MachineReduction.circuit M c d w).input j=OneHead.markedInput (oneHead M) (fun i : Fin (MachineOneHead.input M w).length => (MachineOneHead.input M w)[i]) j := rfl
 theorem circuit_blank (c d : ℕ) (w : Word) : (MachineReduction.circuit M c d w).blank=(default,none) := rfl
 theorem circuit_accepting (c d : ℕ) (w : Word) (f : Letter M) :
    f∈(MachineReduction.circuit M c d w).accepting ↔ (oneHead M).acceptingCell f := Iff.rfl
 theorem listing_good (c d : ℕ) (w : Word) (ε : Affine.Bit) :
    CellularCatalog.Good (n := MachineReduction.internal M c d w) (presentation M)
      (MachineReduction.circuit M c d w) (MachineReduction.marked M c d w) ε
      ((listing M c d ε).eval (fun _=>w.reverse)) := by
  refine ⟨?_,?_,?_,presentation_valid M,?_,?_,?_,?_,?_,?_,?_⟩
  · change (bitProgram M c d).number (fun _=>w.reverse)=MachineReduction.bits M c d w
    rw [bitProgram_number,List.length_reverse]; rfl
  · change (add (numeral 1) (sub (input 0) (numeral 1))).number (fun _=>w.reverse)=(MachineOneHead.input M w).length
    rw [add_number,numeral_number,sub_number,input_number,numeral_number,input_eq,initial_length]
  · exact numeral_number _ _
  · change (mul (numeral 4) (add (add (bitProgram M c d) (bitProgram M c d)) (numeral 1))).number (fun _=>w.reverse)=_
    simp only [mul_number,numeral_number,add_number,bitProgram_number,List.length_reverse,
      MachineReduction.internal,MachineReduction.dimension,MachineReduction.bits]
  · intro a b z
    rw [circuit_rule]
    exact ruleProgram_number M (fun _=>w.reverse) a b z
  · intro j
    change (inputProgram M).number (cons (List.replicate j.val true) (fun _=>w.reverse))=_
    rw [inputProgram_number,letterInput_original,circuit_input]
  · rw [circuit_blank]
    exact numeral_number _ _
  · intro i
    change (acceptProgram M).bit (cons (List.replicate i true) (fun _=>w.reverse))=_
    rw [acceptProgram_bit]
    simp only [acceptCode,circuit_accepting]
  · exact numeral_number _ _
  · exact numeral_number _ _
end VariableWL.MachineCellular

namespace VariableWL
 theorem equivalent_iso_iff {G H G' H' : Graph} (e : G.graph ≃g G'.graph)
    (f : H.graph ≃g H'.graph) (k : ℕ) : Equivalent G H k ↔ Equivalent G' H' k := by
  constructor
  · intro h s
    exact (histogram_iso e k s).trans ((h s).trans (histogram_iso f k s).symm)
  · intro h s
    exact (histogram_iso e k s).symm.trans ((h s).trans (histogram_iso f k s))
 theorem order_eq_of_iso {G H : Graph} (e : G.graph ≃g H.graph) : G.order=H.order := by
  simpa only [Fintype.card_fin] using Fintype.card_congr e.toEquiv
 theorem subcubic_iso_iff {G H : Graph} (e : G.graph ≃g H.graph) : Subcubic G ↔ Subcubic H := by
  classical
  constructor
  · intro h v
    obtain ⟨u,rfl⟩ := e.surjective v
    rw [e.degree_eq u]
    exact h u
  · intro h v
    rw [←e.degree_eq v]
    exact h (e v)
end VariableWL

end OAI
