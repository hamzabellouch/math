import OAI.Combinatorics.VariableWL.CellularCatalog

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.CellularCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable1} {d m n : ℕ} (P : Presentation L) (C : ProductCellular.Data L d m)
variable (marked : Fin (d+d)) (ε : Bit)
structure Good (D : Data) : Prop where
  bits : D.bits=d
  inputLength : D.inputLength=m
  letters : D.letters=P.bound
  valid : P.valid=fun _=>true
  internal : D.internal=n
  rule : ∀a b c,D.rule (P.encode a) (P.encode b) (P.encode c)=P.encode (C.rule a b c)
  input : ∀j : Fin m,D.input j.val=P.encode (C.input j)
  blank : D.blank=P.encode C.blank
  accepting : ∀i,D.accepting i=decide (∃f,P.encode f=i ∧ f∈C.accepting)
  marked : D.marked=marked.val
  epsilon : D.epsilon=ε.val
variable {D : Data} (h : Good (n := n) P C marked ε D)
include h
 theorem kinds_eq : D.kinds=(kind d).bound := by
  simp only [Data.kinds,Data.rightEnd,Data.centerEnd,Data.leftEnd,h.bits,kind,
    Presentation.sum_bound,Presentation.product_bound,Presentation.option_bound,Presentation.fin_bound,Presentation.boolean_bound]
  omega
 theorem triples_eq : D.triples=(triple P).bound := by
  simp only [Data.triples,h.letters,triple,Presentation.product_bound]
 theorem edge_parts (e : ProductCellular.Edge L d) :
    D.tripleCode ((edge P).encode e)=(triple P).encode e.1 ∧ D.kindCode ((edge P).encode e)=(kind d).encode e.2 := by
  have hk := (kind d).encode_lt e.2
  simp only [Data.tripleCode,Data.kindCode,kinds_eq P C marked ε h,edge,Presentation.product_encode]
  exact ⟨PrefixDescriptor.Data.join_div _ _ _ (by omega) hk,PrefixDescriptor.Data.join_mod _ _ _ hk⟩
 theorem triple_parts (a b c : L) :
    D.first ((triple P).encode (a,b,c))=P.encode a ∧
    D.second ((triple P).encode (a,b,c))=P.encode b ∧
    D.third ((triple P).encode (a,b,c))=P.encode c := by
  have ha:=P.encode_lt a
  have hb:=P.encode_lt b
  have hc:=P.encode_lt c
  have hbc := (P.product P).encode_lt (b,c)
  simp only [Presentation.product_encode,Presentation.product_bound] at hbc
  have hp : 0<P.bound := by omega
  change ((P.encode a*(P.bound*P.bound)+(P.encode b*P.bound+P.encode c))/(D.letters*D.letters)=_) ∧ _
  rw [h.letters,PrefixDescriptor.Data.join_div _ _ _ (Nat.mul_pos hp hp) hbc]
  refine ⟨rfl,?_,?_⟩
  · change ((P.encode a*(P.bound*P.bound)+(P.encode b*P.bound+P.encode c))/D.letters)%D.letters=_
    rw [h.letters]
    have he : P.encode a*(P.bound*P.bound)+(P.encode b*P.bound+P.encode c)=
        (P.encode a*P.bound+P.encode b)*P.bound+P.encode c := by ring
    rw [he,PrefixDescriptor.Data.join_div _ _ _ hp hc]
    exact PrefixDescriptor.Data.join_mod _ _ _ hb
  · change (P.encode a*(P.bound*P.bound)+(P.encode b*P.bound+P.encode c))%D.letters=_
    rw [h.letters]
    have he : P.encode a*(P.bound*P.bound)+(P.encode b*P.bound+P.encode c)=
        (P.encode a*P.bound+P.encode b)*P.bound+P.encode c := by ring
    rw [he,PrefixDescriptor.Data.join_mod _ _ _ hc]
 theorem kind_left (j : Fin d) (q : Option (Fin d)) :
    (kind d).encode ((Sum.inl (j,q)))=j.val*(1+D.bits)+(Presentation.fin d).option.encode q := by
  simp only [kind,Presentation.sum_inl,Presentation.product_encode,
    Presentation.option_bound,Presentation.fin_bound,Presentation.fin_encode,h.bits]
 theorem kind_center (j : Fin d) : (kind d).encode ((Sum.inr (Sum.inl j)))=D.leftEnd+j.val := by
  simp only [kind,Presentation.sum_inr,Presentation.sum_inl,
    Presentation.product_bound,Presentation.option_bound,Presentation.fin_bound,Presentation.fin_encode,Data.leftEnd,h.bits]
 theorem kind_right (j : Fin d) (q : Option (Fin d)) :
    (kind d).encode ((Sum.inr (Sum.inr (Sum.inl (j,q)))))=D.centerEnd+(j.val*(1+D.bits)+(Presentation.fin d).option.encode q) := by
  simp only [kind,Presentation.sum_inr,Presentation.sum_inl,Presentation.product_encode,
    Presentation.product_bound,Presentation.option_bound,Presentation.fin_bound,Presentation.fin_encode,Data.centerEnd,Data.leftEnd,h.bits]
  omega
 theorem kind_same (b : Bool) : (kind d).encode ((Sum.inr (Sum.inr (Sum.inr b))))=D.rightEnd+b.toNat := by
  simp only [kind,Presentation.sum_inr,Presentation.product_bound,Presentation.option_bound,
    Presentation.fin_bound,Presentation.boolean_encode,Data.rightEnd,Data.centerEnd,Data.leftEnd,h.bits]
  omega
 theorem left_lt (j : Fin d) (q : Option (Fin d)) : j.val*(1+D.bits)+(Presentation.fin d).option.encode q<D.leftEnd := by
  have hj:=j.isLt
  have hq: (Presentation.fin d).option.encode q<1+d := (Presentation.fin d).option.encode_lt q
  rw [Data.leftEnd,h.bits]
  nlinarith
 theorem left_parts (j : Fin d) (q : Option (Fin d)) :
    D.kindTime ((kind d).encode ((Sum.inl (j,q))))=j.val ∧
    D.kindPosition ((kind d).encode ((Sum.inl (j,q))))=(Presentation.fin d).option.encode q := by
  have hj:=left_lt P C marked ε h j q
  have hq : (Presentation.fin d).option.encode q<1+D.bits := by rw [h.bits]; exact (Presentation.fin d).option.encode_lt q
  rw [kind_left P C marked ε h,Data.kindTime,Data.kindPosition,ite_eq_left hj,ite_eq_left hj]
  exact ⟨PrefixDescriptor.Data.join_div _ _ _ (by omega) hq,PrefixDescriptor.Data.join_mod _ _ _ hq⟩
 theorem center_parts (j : Fin d) : D.kindTime ((kind d).encode ((Sum.inr (Sum.inl j))))=j.val := by
  rw [kind_center P C marked ε h,Data.kindTime,ite_eq_right (by omega),ite_eq_left (by have hj:=j.isLt; rw [Data.centerEnd]; rw [h.bits]; omega)]
  omega
 theorem right_parts (j : Fin d) (q : Option (Fin d)) :
    D.kindTime ((kind d).encode ((Sum.inr (Sum.inr (Sum.inl (j,q))))))=j.val ∧
    D.kindPosition ((kind d).encode ((Sum.inr (Sum.inr (Sum.inl (j,q))))))=(Presentation.fin d).option.encode q := by
  have hq : (Presentation.fin d).option.encode q<1+D.bits := by rw [h.bits]; exact (Presentation.fin d).option.encode_lt q
  have hle : D.leftEnd≤D.centerEnd := by unfold Data.centerEnd; omega
  rw [kind_right P C marked ε h,Data.kindTime,Data.kindPosition,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),Nat.add_sub_cancel_left]
  exact ⟨PrefixDescriptor.Data.join_div _ _ _ (by omega) hq,PrefixDescriptor.Data.join_mod _ _ _ hq⟩
end VariableWL.CellularCatalog

namespace VariableWL.CellularCatalog.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
variable {n : ℕ}
structure Listing (n : ℕ) where
  bits : Expr n
  inputLength : Expr n
  letters : Expr n
  internal : Expr n
  rule : Expr (n+3)
  input : Expr (n+1)
  blank : Expr n
  accepting : Expr (n+1)
  marked : Expr n
  epsilon : Expr n
 theorem bool_ite_nat (b : Bool) : (if b then 1 else 0)=b.toNat := by cases b <;> rfl
namespace Listing
variable (D : Listing n)
def eval (v : Env n) : Data where
  bits := D.bits.number v
  inputLength := D.inputLength.number v
  letters := D.letters.number v
  internal := D.internal.number v
  rule i j a := D.rule.number (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))
  input i := D.input.number (cons (List.replicate i true) v)
  blank := D.blank.number v
  accepting i := D.accepting.bit (cons (List.replicate i true) v)
  marked := D.marked.number v
  epsilon := D.epsilon.number v
def up : Listing (n+1) where
  bits := D.bits.up
  inputLength := D.inputLength.up
  letters := D.letters.up
  internal := D.internal.up
  rule := underThree D.rule
  input := underOne D.input
  blank := D.blank.up
  accepting := underOne D.accepting
  marked := D.marked.up
  epsilon := D.epsilon.up
 theorem eval_up (v : Env n) (a : Word) : D.up.eval (cons a v)=D.eval v := by
  dsimp only [eval,up]
  congr 1
  · funext i j a; exact underThree_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_bit ..
noncomputable def leftEnd : Expr n := (mul D.bits (add (numeral 1) D.bits))
noncomputable def centerEnd : Expr n := (add D.leftEnd D.bits)
noncomputable def rightEnd : Expr n := (add D.centerEnd D.leftEnd)
noncomputable def kinds : Expr n := (add D.rightEnd (numeral 2))
noncomputable def triples : Expr n := (mul D.letters (mul D.letters D.letters))
noncomputable def tripleCode (E : Expr n) : Expr n := (div E D.kinds)
noncomputable def kindCode (E : Expr n) : Expr n := (mod E D.kinds)
noncomputable def first (T : Expr n) : Expr n := (div T (mul D.letters D.letters))
noncomputable def second (T : Expr n) : Expr n := (mod (div T D.letters) D.letters)
noncomputable def third (T : Expr n) : Expr n := (mod T D.letters)
noncomputable def kindTime (K : Expr n) : Expr n := (choose (lt K D.leftEnd) (div K (add (numeral 1) D.bits)) (choose (lt K D.centerEnd) (sub K D.leftEnd) (div (sub K D.centerEnd) (add (numeral 1) D.bits))))
noncomputable def kindPosition (K : Expr n) : Expr n := (choose (lt K D.leftEnd) (mod K (add (numeral 1) D.bits)) (mod (sub K D.centerEnd) (add (numeral 1) D.bits)))
noncomputable def source (E : Expr n) : Expr n := (choose (lt (D.kindCode E) D.leftEnd) (D.first (D.tripleCode E)) (choose (lt (D.kindCode E) D.centerEnd) (D.second (D.tripleCode E)) (choose (lt (D.kindCode E) D.rightEnd) (D.third (D.tripleCode E)) (add D.letters (add (mul (D.tripleCode E) (numeral 2)) (sub (D.kindCode E) D.rightEnd))))))
noncomputable def destination (E : Expr n) : Expr n := (choose (lt (D.kindCode E) D.centerEnd) (add D.letters (mul (D.tripleCode E) (numeral 2))) (choose (lt (D.kindCode E) (add D.rightEnd (numeral 1))) (add D.letters (add (mul (D.tripleCode E) (numeral 2)) (numeral 1))) (applyNat₃ D.rule (D.first (D.tripleCode E)) (D.second (D.tripleCode E)) (D.third (D.tripleCode E)))))
noncomputable def destinationForm (E : Expr n) : Expr n := (choose (lt (D.kindCode E) D.leftEnd) (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 0))) (choose (lt (D.kindCode E) D.rightEnd) (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 1))) (choose (lt (D.kindCode E) (add D.rightEnd (numeral 1))) (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 0))) (numeral (AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0))))))
def carryDomain (_D : Listing n) (B H I A : Expr n) : Expr n := (choose (lt I H) (eq A B) (choose (eq I H) (eq A (sub (numeral 1) B)) (literal [true])))
def cyclicDomain (D : Listing n) (B H I A : Expr n) : Expr n := (choose (eq H (numeral 0)) (eq A B) (D.carryDomain B (sub H (numeral 1)) I A))
noncomputable def domain (E I A : Expr n) : Expr n := (choose (lt (D.kindCode E) D.rightEnd) (choose (lt I D.bits) (D.carryDomain (numeral 1) (D.kindTime (D.kindCode E)) I A) (choose (lt (D.kindCode E) D.leftEnd) (D.cyclicDomain (numeral 1) (D.kindPosition (D.kindCode E)) (sub I D.bits) A) (choose (lt (D.kindCode E) D.centerEnd) (literal [true]) (D.cyclicDomain (numeral 0) (D.kindPosition (D.kindCode E)) (sub I D.bits) A)))) (literal [true]))
noncomputable def map (E I A : Expr n) : Expr n := (choose (lt (D.kindCode E) D.rightEnd) (choose (lt I D.bits) (choose (le I (D.kindTime (D.kindCode E))) (sub (numeral 1) A) A) (choose (disj (lt (D.kindCode E) D.leftEnd) (le D.centerEnd (D.kindCode E))) (choose (disj (eq (D.kindPosition (D.kindCode E)) (numeral 0)) (lt (sub I D.bits) (D.kindPosition (D.kindCode E)))) (sub (numeral 1) A) A) A)) A)
noncomputable def initialEnd : Expr n := (add D.inputLength (add (numeral 1) D.bits))
noncomputable def validRequest (B : Expr n) : Expr n := (choose (lt B D.inputLength) (literal [true]) (choose (eq B D.inputLength) (literal [true]) (choose (lt B D.initialEnd) (neg (binaryDigit D.inputLength (sub (sub B D.inputLength) (numeral 1)))) (applyNat D.accepting (sub B D.initialEnd)))))
noncomputable def requestGate (B : Expr n) : Expr n := (choose (lt B D.inputLength) (applyNat D.input B) (choose (lt B D.initialEnd) D.blank (sub B D.initialEnd)))
noncomputable def requestTest (B : Expr n) : Expr n := (choose (lt B D.initialEnd) (numeral 0) (numeral 1))
noncomputable def requestPositionDomain (B I A : Expr n) : Expr n := (choose (lt B D.inputLength) (eq A (choose (binaryDigit B I) (numeral 1) (numeral 0))) (choose (lt B D.initialEnd) (choose (disj (eq B D.inputLength) (lt (sub (sub B D.inputLength) (numeral 1)) I)) (eq A (choose (binaryDigit D.inputLength I) (numeral 1) (numeral 0))) (choose (eq I (sub (sub B D.inputLength) (numeral 1))) (eq A (numeral 1)) (literal [true]))) (literal [true])))
noncomputable def requestDomain (B I A : Expr n) : Expr n := (choose (lt I D.bits) (eq A (D.requestTest B)) (D.requestPositionDomain B (sub I D.bits) A))
 theorem leftEnd_number (v : Env n) : (D.leftEnd).number v=(D.eval v).leftEnd := by
  simp only [leftEnd,add_number,mul_number,numeral_number,eval,Data.leftEnd]
 theorem centerEnd_number (v : Env n) : (D.centerEnd).number v=(D.eval v).centerEnd := by
  simp only [centerEnd,leftEnd_number,add_number,eval,Data.centerEnd]
 theorem rightEnd_number (v : Env n) : (D.rightEnd).number v=(D.eval v).rightEnd := by
  simp only [rightEnd,leftEnd_number,centerEnd_number,add_number,eval,Data.rightEnd]
 theorem kinds_number (v : Env n) : (D.kinds).number v=(D.eval v).kinds := by
  simp only [kinds,rightEnd_number,add_number,numeral_number,eval,Data.kinds]
 theorem triples_number (v : Env n) : (D.triples).number v=(D.eval v).triples := by
  simp only [triples,mul_number,eval,Data.triples]
 theorem tripleCode_number (E : Expr n) (v : Env n) : (D.tripleCode E).number v=(D.eval v).tripleCode (E.number v) := by
  simp only [tripleCode,kinds_number,div_number,eval,Data.tripleCode]
 theorem kindCode_number (E : Expr n) (v : Env n) : (D.kindCode E).number v=(D.eval v).kindCode (E.number v) := by
  simp only [kindCode,kinds_number,mod_number,eval,Data.kindCode]
 theorem first_number (T : Expr n) (v : Env n) : (D.first T).number v=(D.eval v).first (T.number v) := by
  simp only [first,mul_number,div_number,eval,Data.first]
 theorem second_number (T : Expr n) (v : Env n) : (D.second T).number v=(D.eval v).second (T.number v) := by
  simp only [second,div_number,mod_number,eval,Data.second]
 theorem third_number (T : Expr n) (v : Env n) : (D.third T).number v=(D.eval v).third (T.number v) := by
  simp only [third,mod_number,eval,Data.third]
 theorem kindTime_number (K : Expr n) (v : Env n) : (D.kindTime K).number v=(D.eval v).kindTime (K.number v) := by
  simp only [kindTime,leftEnd_number,centerEnd_number,choose_number,add_number,sub_number,div_number,numeral_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.kindTime] ; rfl
 theorem kindPosition_number (K : Expr n) (v : Env n) : (D.kindPosition K).number v=(D.eval v).kindPosition (K.number v) := by
  simp only [kindPosition,leftEnd_number,centerEnd_number,choose_number,add_number,sub_number,mod_number,numeral_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.kindPosition] ; rfl
 theorem source_number (E : Expr n) (v : Env n) : (D.source E).number v=(D.eval v).source (E.number v) := by
  simp only [source,leftEnd_number,centerEnd_number,rightEnd_number,tripleCode_number,kindCode_number,first_number,second_number,third_number,choose_number,add_number,mul_number,sub_number,numeral_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.source] ; rfl
 theorem destination_number (E : Expr n) (v : Env n) : (D.destination E).number v=(D.eval v).destination (E.number v) := by
  simp only [destination,centerEnd_number,rightEnd_number,tripleCode_number,kindCode_number,first_number,second_number,third_number,applyNat₃_number,choose_number,add_number,mul_number,numeral_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.destination] ; rfl
 theorem destinationForm_number (E : Expr n) (v : Env n) : (D.destinationForm E).number v=(D.eval v).destinationForm (E.number v) := by
  simp only [destinationForm,leftEnd_number,rightEnd_number,kindCode_number,choose_number,add_number,numeral_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.destinationForm] ; rfl
 theorem carryDomain_bit (B H I A : Expr n) (v : Env n) : (D.carryDomain B H I A).bit v=Data.carryDomain (B.number v) (H.number v) (I.number v) (A.number v) := by
  simp only [carryDomain,choose_bit,sub_number,numeral_number,eq_bit,lt_bit,BlockCatalog.Program.literal_true_bit,decide_eq_true_eq,decide_eq_true_eq,Data.carryDomain]
 theorem cyclicDomain_bit (B H I A : Expr n) (v : Env n) : (D.cyclicDomain B H I A).bit v=Data.cyclicDomain (B.number v) (H.number v) (I.number v) (A.number v) := by
  simp only [cyclicDomain,carryDomain_bit,choose_bit,sub_number,numeral_number,eq_bit,decide_eq_true_eq,decide_eq_true_eq,Data.cyclicDomain]
 theorem domain_bit (E I A : Expr n) (v : Env n) : (D.domain E I A).bit v=(D.eval v).domain (E.number v) (I.number v) (A.number v) := by
  simp only [domain,leftEnd_number,centerEnd_number,rightEnd_number,kindCode_number,kindTime_number,kindPosition_number,carryDomain_bit,cyclicDomain_bit,choose_bit,sub_number,numeral_number,lt_bit,BlockCatalog.Program.literal_true_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.domain] ; rfl
 theorem map_number (E I A : Expr n) (v : Env n) : (D.map E I A).number v=(D.eval v).map (E.number v) (I.number v) (A.number v) := by
  simp only [map,leftEnd_number,centerEnd_number,rightEnd_number,kindCode_number,kindTime_number,kindPosition_number,choose_number,sub_number,numeral_number,eq_bit,lt_bit,le_bit,disj_bit,decide_eq_true_eq,Bool.or_eq_true,decide_eq_true_eq,eval,Data.map] ; rfl
 theorem initialEnd_number (v : Env n) : (D.initialEnd).number v=(D.eval v).initialEnd := by
  simp only [initialEnd,add_number,numeral_number,eval,Data.initialEnd]
 theorem validRequest_bit (B : Expr n) (v : Env n) : (D.validRequest B).bit v=(D.eval v).validRequest (B.number v) := by
  simp only [validRequest,initialEnd_number,applyNat_bit,choose_bit,sub_number,numeral_number,eq_bit,lt_bit,neg_bit,binaryDigit_total,BlockCatalog.Program.literal_true_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.validRequest] ; rfl
 theorem requestGate_number (B : Expr n) (v : Env n) : (D.requestGate B).number v=(D.eval v).requestGate (B.number v) := by
  simp only [requestGate,initialEnd_number,applyNat_number,choose_number,sub_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.requestGate] ; rfl
 theorem requestTest_number (B : Expr n) (v : Env n) : (D.requestTest B).number v=(D.eval v).requestTest (B.number v) := by
  simp only [requestTest,initialEnd_number,choose_number,numeral_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.requestTest] ; rfl
 theorem requestPositionDomain_bit (B I A : Expr n) (v : Env n) : (D.requestPositionDomain B I A).bit v=(D.eval v).requestPositionDomain (B.number v) (I.number v) (A.number v) := by
  simp only [requestPositionDomain,initialEnd_number,choose_number,choose_bit,sub_number,numeral_number,eq_bit,lt_bit,disj_bit,binaryDigit_total,BlockCatalog.Program.literal_true_bit,decide_eq_true_eq,Bool.or_eq_true,decide_eq_true_eq,bool_ite_nat,eval,Data.requestPositionDomain] ; rfl
 theorem requestDomain_bit (B I A : Expr n) (v : Env n) : (D.requestDomain B I A).bit v=(D.eval v).requestDomain (B.number v) (I.number v) (A.number v) := by
  simp only [requestDomain,requestTest_number,requestPositionDomain_bit,choose_bit,sub_number,eq_bit,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.requestDomain] ; rfl
noncomputable def catalog : CircuitCatalog.Program.Listing n where
  rows := add D.bits D.bits
  internal := D.internal
  scalars := D.letters
  ands := mul D.triples (numeral 2)
  edges := mul D.triples D.kinds
  requests := add D.initialEnd D.letters
  validScalar := literal [true]
  validAnd := literal [true]
  validEdge := literal [true]
  validRequest := D.up.validRequest (Computation.Stack.PolyRecipe.input 0)
  source := D.up.source (Computation.Stack.PolyRecipe.input 0)
  destination := D.up.destination (Computation.Stack.PolyRecipe.input 0)
  destinationForm := D.up.destinationForm (Computation.Stack.PolyRecipe.input 0)
  domain := D.up.up.up.domain (Computation.Stack.PolyRecipe.input 0) (Computation.Stack.PolyRecipe.input 1) (Computation.Stack.PolyRecipe.input 2)
  map := D.up.up.up.map (Computation.Stack.PolyRecipe.input 0) (Computation.Stack.PolyRecipe.input 1) (Computation.Stack.PolyRecipe.input 2)
  requestGate := D.up.requestGate (Computation.Stack.PolyRecipe.input 0)
  requestTest := D.up.requestTest (Computation.Stack.PolyRecipe.input 0)
  requestDomain := D.up.up.up.requestDomain (Computation.Stack.PolyRecipe.input 0) (Computation.Stack.PolyRecipe.input 1) (Computation.Stack.PolyRecipe.input 2)
  marked := D.marked
  epsilon := D.epsilon
end Listing
end VariableWL.CellularCatalog.Program

namespace VariableWL.CellularCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable2} {d m n : ℕ} (P : Presentation L) (C : ProductCellular.Data L d m)
variable (marked : Fin (d+d)) (ε : Bit) {D : Data} (h : Good (n := n) P C marked ε D)
include h
 theorem left_bounds (j : Fin d) (q : Option (Fin d)) :
    (kind d).encode ((Sum.inl (j,q)))<D.leftEnd ∧
    (kind d).encode ((Sum.inl (j,q)))<D.centerEnd ∧
    (kind d).encode ((Sum.inl (j,q)))<D.rightEnd := by
  have ha:=left_lt P C marked ε h j q
  rw [←kind_left P C marked ε h] at ha
  dsimp only [Data.centerEnd,Data.rightEnd]
  omega
 theorem center_bounds (j : Fin d) :
    D.leftEnd≤(kind d).encode ((Sum.inr (Sum.inl j))) ∧
    (kind d).encode ((Sum.inr (Sum.inl j)))<D.centerEnd ∧
    (kind d).encode ((Sum.inr (Sum.inl j)))<D.rightEnd := by
  rw [kind_center P C marked ε h]
  have hj:=j.isLt
  dsimp only [Data.centerEnd,Data.rightEnd]
  rw [h.bits]
  omega
 theorem right_bounds (j : Fin d) (q : Option (Fin d)) :
    D.leftEnd≤(kind d).encode ((Sum.inr (Sum.inr (Sum.inl (j,q))))) ∧
    D.centerEnd≤(kind d).encode ((Sum.inr (Sum.inr (Sum.inl (j,q))))) ∧
    (kind d).encode ((Sum.inr (Sum.inr (Sum.inl (j,q)))))<D.rightEnd := by
  rw [kind_right P C marked ε h]
  have ha:=left_lt P C marked ε h j q
  dsimp only [Data.rightEnd,Data.centerEnd]
  omega
 theorem same_bounds (b : Bool) :
    D.leftEnd≤(kind d).encode ((Sum.inr (Sum.inr (Sum.inr b)))) ∧
    D.centerEnd≤(kind d).encode ((Sum.inr (Sum.inr (Sum.inr b)))) ∧
    D.rightEnd≤(kind d).encode ((Sum.inr (Sum.inr (Sum.inr b)))) := by
  rw [kind_same P C marked ε h]
  dsimp only [Data.rightEnd,Data.centerEnd]
  omega
 theorem source_eq (e : ProductCellular.Edge L d) :
    D.source ((edge P).encode e)=(P.sum (ands P)).encode (ProductCellular.source e) := by
  rcases e with ⟨⟨a,b,c⟩,k⟩
  rw [Data.source,(edge_parts P C marked ε h ((a,b,c),k)).1,(edge_parts P C marked ε h ((a,b,c),k)).2]
  have ht:=triple_parts P C marked ε h a b c
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.1,ht.1]; rfl
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_right (by omega),ite_eq_left hb.2.1,ht.2.1]; rfl
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left hb.2.2,ht.2.2]; rfl
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),kind_same P C marked ε h,Nat.add_sub_cancel_left,h.letters]
    rfl
 theorem destination_eq (e : ProductCellular.Edge L d) :
    D.destination ((edge P).encode e)=(P.sum (ands P)).encode (target L (Cellular.Triple L × Bool) (ProductCellular.destination C.rule e)) := by
  rcases e with ⟨⟨a,b,c⟩,k⟩
  rw [Data.destination,(edge_parts P C marked ε h ((a,b,c),k)).1,(edge_parts P C marked ε h ((a,b,c),k)).2]
  have ht:=triple_parts P C marked ε h a b c
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.1,h.letters]
    simp only [ProductCellular.destination,target,Presentation.sum_inr,ands,Presentation.product_encode,Presentation.boolean_bound,Presentation.boolean_encode,Bool.toNat_false,Nat.add_zero]
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_left hb.2.1,h.letters]
    simp only [ProductCellular.destination,target,Presentation.sum_inr,ands,Presentation.product_encode,Presentation.boolean_bound,Presentation.boolean_encode,Bool.toNat_false,Nat.add_zero]
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_right (by omega),ite_eq_left (by omega),h.letters]
    rfl
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega),kind_same P C marked ε h]
    cases v
    · rw [Bool.toNat_false,Nat.add_zero,ite_eq_left (by omega),h.letters]; rfl
    · rw [Bool.toNat_true,ite_eq_right (by omega),ht.1,ht.2.1,ht.2.2,h.rule]; rfl
 theorem destinationForm_eq (e : ProductCellular.Edge L d) :
    D.destinationForm ((edge P).encode e)=AffineAlphabet.encodeForm
      (by cases ProductCellular.destination C.rule e <;> simp only [dimension] <;> decide)
      (inputLinear (ProductCellular.destination C.rule e)) := by
  rcases e with ⟨abc,k⟩
  rw [Data.destinationForm,(edge_parts P C marked ε h (abc,k)).2]
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.1]; rfl
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_right (by omega),ite_eq_left hb.2.2]; rfl
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_right (by omega),ite_eq_left hb.2.2]; rfl
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega),ite_eq_right (by omega),kind_same P C marked ε h]
    cases v
    · rw [Bool.toNat_false,Nat.add_zero,ite_eq_left (by omega)]; rfl
    · rw [Bool.toNat_true,ite_eq_right (by omega)]; rfl
end VariableWL.CellularCatalog

namespace VariableWL.CellularCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
 theorem bool_nat_eq (a b : Bool) : a.toNat=b.toNat ↔ a=b := by cases a <;> cases b <;> decide
 theorem carryDomain_eq {d : ℕ} (bit a : Bool) (h i : Fin d) :
    Data.carryDomain bit.toNat h.val i.val a.toNat=true ↔ a∈Binary.domain bit h i := by
  simp only [Data.carryDomain,Binary.domain,Fin.lt_def,Fin.ext_iff]
  split_ifs <;> cases bit <;> cases a <;> simp_all
 theorem cyclicDomain_eq {d : ℕ} (bit a : Bool) (q : Option (Fin d)) (i : Fin d) :
    Data.cyclicDomain bit.toNat ((Presentation.fin d).option.encode q) i.val a.toNat=true ↔ a∈Binary.cyclicDomain bit q i := by
  cases q with
  | none => simp only [Data.cyclicDomain,Presentation.option_none,ite_true,Binary.cyclicDomain,decide_eq_true_eq,Finset.mem_singleton,bool_nat_eq]
  | some j =>
    simp only [Data.cyclicDomain,Presentation.option_some,Presentation.fin_encode,
      ite_eq_right (show ¬1+j.val=0 by omega),show 1+j.val-1=j.val by omega,Binary.cyclicDomain]
    exact carryDomain_eq bit a j i
 theorem carryMap_eq {d : ℕ} (h i : Fin d) (a : Bool) :
    (if i.val≤h.val then 1-a.toNat else a.toNat)=(Binary.table h i a).toNat := by
  simp only [Binary.table,Fin.le_def]
  split_ifs <;> cases a <;> rfl
 theorem cyclicMap_eq {d : ℕ} (q : Option (Fin d)) (i : Fin d) (a : Bool) :
    (if (Presentation.fin d).option.encode q=0 ∨ i.val<(Presentation.fin d).option.encode q then 1-a.toNat else a.toNat)=
      (Binary.cyclicTable q i a).toNat := by
  cases q with
  | none => simp only [Presentation.option_none,true_or,ite_true,Binary.cyclicTable]; cases a <;> rfl
  | some j =>
    simp only [Presentation.option_some,Presentation.fin_encode,Binary.cyclicTable]
    simpa only [show (1+j.val=0 ∨ i.val<1+j.val) ↔ i.val≤j.val by omega] using carryMap_eq j i a
variable {L : Type uVariable3} {d m n : ℕ} (P : Presentation L) (C : ProductCellular.Data L d m)
variable (marked : Fin (d+d)) (ε : Bit) {D : Data} (h : Good (n := n) P C marked ε D)
include h
 theorem domain_time (e : ProductCellular.Edge L d) (i : Fin d) (a : Bool) :
    D.domain ((edge P).encode e) (i.castAdd d).val a.toNat=true ↔ a∈ProductCellular.timeDomain e.2 i := by
  rcases e with ⟨abc,k⟩
  rw [Data.domain,(edge_parts P C marked ε h (abc,k)).2]
  have hi : (i.castAdd d).val<D.bits := by simpa only [Fin.val_castAdd,h.bits] using i.isLt
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_left hi,(left_parts P C marked ε h j q).1]
    exact carryDomain_eq true a j i
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_left hb.2.2,ite_eq_left hi,center_parts P C marked ε h j]
    exact carryDomain_eq true a j i
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_left hi,(right_parts P C marked ε h j q).1]
    exact carryDomain_eq true a j i
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega)]; simp only [ProductCellular.timeDomain,Finset.mem_univ]
 theorem domain_position (e : ProductCellular.Edge L d) (i : Fin d) (a : Bool) :
    D.domain ((edge P).encode e) (Fin.natAdd d i).val a.toNat=true ↔ a∈ProductCellular.positionDomain e.2 i := by
  rcases e with ⟨abc,k⟩
  rw [Data.domain,(edge_parts P C marked ε h (abc,k)).2]
  have hi : ¬(Fin.natAdd d i).val<D.bits := by simp only [Fin.val_natAdd,h.bits]; omega
  have hs : (Fin.natAdd d i).val-D.bits=i.val := by simp only [Fin.val_natAdd,h.bits,Nat.add_sub_cancel_left]
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_right hi,ite_eq_left hb.1,(left_parts P C marked ε h j q).2,hs]
    exact cyclicDomain_eq true a q i
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_left hb.2.2,ite_eq_right hi,ite_eq_right (by omega),ite_eq_left hb.2.1]
    simp only [ProductCellular.positionDomain,Finset.mem_univ]
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_right hi,ite_eq_right (by omega),ite_eq_right (by omega),(right_parts P C marked ε h j q).2,hs]
    exact cyclicDomain_eq false a q i
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega)]; simp only [ProductCellular.positionDomain,Finset.mem_univ]
 theorem domain_eq (e : ProductCellular.Edge L d) (i : Fin (d+d)) (a : Bool) :
    D.domain ((edge P).encode e) i.val a.toNat=true ↔ a∈C.description.domain e i := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simpa only [ProductCellular.Data.description,ProductCellular.join_left] using domain_time P C marked ε h e j a
  · simpa only [ProductCellular.Data.description,ProductCellular.join_right] using domain_position P C marked ε h e j a
 theorem map_time (e : ProductCellular.Edge L d) (i : Fin d) (a : Bool) :
    D.map ((edge P).encode e) (i.castAdd d).val a.toNat=(ProductCellular.timeMap e.2 i a).toNat := by
  rcases e with ⟨abc,k⟩
  rw [Data.map,(edge_parts P C marked ε h (abc,k)).2]
  have hi : (i.castAdd d).val<D.bits := by simpa only [Fin.val_castAdd,h.bits] using i.isLt
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_left hi,(left_parts P C marked ε h j q).1]
    exact carryMap_eq j i a
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_left hb.2.2,ite_eq_left hi,center_parts P C marked ε h j]
    exact carryMap_eq j i a
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_left hi,(right_parts P C marked ε h j q).1]
    exact carryMap_eq j i a
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega)]; rfl
 theorem map_position (e : ProductCellular.Edge L d) (i : Fin d) (a : Bool) :
    D.map ((edge P).encode e) (Fin.natAdd d i).val a.toNat=(ProductCellular.positionMap e.2 i a).toNat := by
  rcases e with ⟨abc,k⟩
  rw [Data.map,(edge_parts P C marked ε h (abc,k)).2]
  have hi : ¬(Fin.natAdd d i).val<D.bits := by simp only [Fin.val_natAdd,h.bits]; omega
  have hs : (Fin.natAdd d i).val-D.bits=i.val := by simp only [Fin.val_natAdd,h.bits,Nat.add_sub_cancel_left]
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_right hi,ite_eq_left (Or.inl hb.1),(left_parts P C marked ε h j q).2,hs]
    exact cyclicMap_eq q i a
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_left hb.2.2,ite_eq_right hi,ite_eq_right (by omega)]; rfl
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_right hi,ite_eq_left (Or.inr hb.2.1),(right_parts P C marked ε h j q).2,hs]
    exact cyclicMap_eq q i a
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega)]; rfl
 theorem map_eq (e : ProductCellular.Edge L d) (i : Fin (d+d)) (a : Bool) :
    D.map ((edge P).encode e) i.val a.toNat=(C.description.map e i a).toNat := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simpa only [ProductCellular.Data.description,ProductCellular.join_left] using map_time P C marked ε h e j a
  · simpa only [ProductCellular.Data.description,ProductCellular.join_right] using map_position P C marked ε h e j a
end VariableWL.CellularCatalog

namespace VariableWL.CellularCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable4} {d m n : ℕ} (P : Presentation L) (C : ProductCellular.Data L d m)
variable (marked : Fin (d+d)) (ε : Bit) {D : Data} (h : Good (n := n) P C marked ε D)
include h
omit h in
 theorem request_first (j : Fin m) : (request P C).encode (.inl (.inl j))=j.val := rfl
omit h in
 theorem request_none : (request P C).encode (.inl (.inr none))=m := by
  simp only [request,Presentation.sum_inl,Presentation.sum_inr,Presentation.fin_bound,Presentation.option_none,Nat.add_zero]
omit h in
 theorem request_some (j : {i : Fin d // C.threshold i=false}) :
    (request P C).encode (.inl (.inr (some j)))=m+(1+j.val.val) := rfl
 theorem request_accepting (f : {a : L // a∈C.accepting}) :
    (request P C).encode (.inr f)=D.initialEnd+P.encode f.val := by
  simp only [request,Presentation.sum_inr,Presentation.sum_bound,Presentation.option_bound,
    Presentation.fin_bound,zeroBit,Presentation.filter_bound,accepting,Presentation.filter_encode,Data.initialEnd,h.bits,h.inputLength]
 theorem initialEnd_eq : D.initialEnd=m+(1+d) := by rw [Data.initialEnd,h.bits,h.inputLength]
 theorem request_gate (b : C.Request) : D.requestGate ((request P C).encode b)=P.encode (C.requestGate b) := by
  rcases b with (j|q)|f
  · rw [request_first P C,Data.requestGate,ite_eq_left (by rw [h.inputLength]; exact j.isLt),h.input]; rfl
  · cases q with
    | none => rw [request_none P C,Data.requestGate,h.inputLength,ite_eq_right (by omega),initialEnd_eq P C marked ε h,ite_eq_left (by omega),h.blank]; rfl
    | some j =>
      rw [request_some P C,Data.requestGate,h.inputLength,ite_eq_right (by omega),initialEnd_eq P C marked ε h,ite_eq_left (by have:=j.val.isLt; omega),h.blank]; rfl
  · rw [request_accepting P C marked ε h,Data.requestGate,ite_eq_right (by rw [initialEnd_eq P C marked ε h,h.inputLength]; omega),ite_eq_right (by omega),Nat.add_sub_cancel_left]; rfl
 theorem request_test (b : C.Request) : D.requestTest ((request P C).encode b)=(if C.requestTest b then 1 else 0) := by
  rcases b with (j|q)|f
  · rw [request_first P C,Data.requestTest,initialEnd_eq P C marked ε h,ite_eq_left (by have:=j.isLt; omega)]; rfl
  · cases q with
    | none => rw [request_none P C,Data.requestTest,initialEnd_eq P C marked ε h,ite_eq_left (by omega)]; rfl
    | some j => rw [request_some P C,Data.requestTest,initialEnd_eq P C marked ε h,ite_eq_left (by have:=j.val.isLt; omega)]; rfl
  · rw [request_accepting P C marked ε h,Data.requestTest,ite_eq_right (by omega)]; rfl
 theorem request_position (b : C.Request) (i : Fin d) (a : Bool) :
    D.requestPositionDomain ((request P C).encode b) i.val a.toNat=true ↔ a∈C.requestPositionDomain b i := by
  rcases b with (j|q)|f
  · rw [request_first P C,Data.requestPositionDomain,ite_eq_left (by rw [h.inputLength]; exact j.isLt),C.input_bit j i]
    simp only [decide_eq_true_eq,bool_nat_eq,ProductCellular.Data.requestPositionDomain,Finset.mem_singleton]
  · cases q with
    | none =>
      rw [request_none P C,Data.requestPositionDomain,h.inputLength,ite_eq_right (by omega),initialEnd_eq P C marked ε h,ite_eq_left (by omega),ite_eq_left (Or.inl rfl),C.threshold_bit i]
      simp only [decide_eq_true_eq,bool_nat_eq,ProductCellular.Data.requestPositionDomain,Binary.thresholdDomain,Finset.mem_singleton]
    | some j =>
      rw [request_some P C,Data.requestPositionDomain,h.inputLength,ite_eq_right (by omega),initialEnd_eq P C marked ε h,ite_eq_left (by have:=j.val.isLt; omega)]
      have hs : m+(1+j.val.val)-m-1=j.val.val := by omega
      simp only [hs,show (m+(1+j.val.val)=m ∨ j.val.val < i.val) ↔ j.val.val < i.val by omega]
      conv_lhs => rw [C.threshold_bit i]
      simp only [ProductCellular.Data.requestPositionDomain,Binary.thresholdDomain,Fin.lt_def,Fin.ext_iff]
      split_ifs <;> cases a <;> cases hi : C.threshold i <;> simp_all
  · rw [request_accepting P C marked ε h,Data.requestPositionDomain,
      ite_eq_right (by rw [initialEnd_eq P C marked ε h,h.inputLength]; omega),ite_eq_right (by omega)]
    simp only [ProductCellular.Data.requestPositionDomain,Finset.mem_univ]
 theorem request_domain (b : C.Request) (i : Fin (d+d)) (a : Bool) :
    D.requestDomain ((request P C).encode b) i.val a.toNat=true ↔ a∈C.description.requestDomain b i := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · rw [Data.requestDomain,ite_eq_left (by simpa only [h.bits,Fin.val_castAdd] using j.isLt),request_test P C marked ε h]
    simp only [ProductCellular.Data.description,ProductCellular.join_left]
    rcases b with (t|q)|f <;> cases a <;> simp only [ProductCellular.Data.requestTest,
      ProductCellular.Data.requestTimeDomain,Bool.false_eq_true,ite_false,ite_true,Bool.toNat_true,Bool.toNat_false,
      decide_true,Finset.mem_singleton] <;> decide
  · rw [Data.requestDomain,ite_eq_right (by simp only [h.bits,Fin.val_natAdd]; omega)]
    have hs : (Fin.natAdd d j).val-D.bits=j.val := by simp only [Fin.val_natAdd,h.bits,Nat.add_sub_cancel_left]
    rw [hs]
    simpa only [ProductCellular.Data.description,ProductCellular.join_right] using request_position P C marked ε h b j a
 theorem valid_request : D.validRequest=(request P C).valid := by
  funext b
  simp only [Data.validRequest,request,Presentation.sum_valid,Presentation.fin_valid,
    Presentation.fin_bound,Presentation.option_valid,Presentation.sum_bound,Presentation.option_bound,
    zeroBit,Presentation.filter_bound,Presentation.filter_valid,accepting,h.valid,Bool.true_and,
    h.inputLength,initialEnd_eq P C marked ε h,Presentation.fin_bound,h.accepting]
  by_cases hb : b < m
  · simp only [ite_eq_left hb,ite_eq_left (by omega : b < m+(1+d))]
  · rw [ite_eq_right hb]
    by_cases he : b=m
    · subst b; simp
    · by_cases hc : b < m+(1+d)
      · simp only [ite_eq_left hc,ite_eq_right he,ite_eq_right hb,ite_eq_right (by omega : ¬ b - m < 1)]
      · simp only [ite_eq_right hc,ite_eq_right he]
 theorem and_valid : (ands P).valid=fun _=>true := by
  funext i
  simp only [ands,triple,Presentation.product_valid,Presentation.boolean_valid,h.valid,Bool.true_and]
 theorem edge_valid : (edge (d := d) P).valid=fun _=>true := by
  funext i
  simp only [edge,triple,kind,Presentation.product_valid,Presentation.sum_valid,Presentation.option_valid,
    Presentation.fin_valid,Presentation.boolean_valid,h.valid,Bool.true_and,ite_self]
 theorem catalog_good : CircuitCatalog.Good (n := n) P (ands P) (edge P) (request P C) C.description marked ε D.catalog := by
  refine ⟨?_,h.internal,h.letters,?_,?_,?_,h.valid.symm,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.marked,h.epsilon⟩
  · change D.bits+D.bits=d+d; rw [h.bits]
  · change D.triples*2=(ands P).bound
    rw [triples_eq P C marked ε h]; rfl
  · change D.triples*D.kinds=(edge P).bound
    rw [triples_eq P C marked ε h,kinds_eq P C marked ε h]; rfl
  · change D.initialEnd+D.letters=(request P C).bound
    simp only [initialEnd_eq P C marked ε h,h.letters,request,Presentation.sum_bound,Presentation.option_bound,
      Presentation.fin_bound,zeroBit,Presentation.filter_bound,accepting]
  · exact (and_valid P C marked ε h).symm
  · exact (edge_valid P C marked ε h).symm
  · exact valid_request P C marked ε h
  · exact source_eq P C marked ε h
  · exact destination_eq P C marked ε h
  · exact destinationForm_eq P C marked ε h
  · exact domain_eq P C marked ε h
  · exact map_eq P C marked ε h
  · exact request_gate P C marked ε h
  · exact request_test P C marked ε h
  · exact request_domain P C marked ε h
end VariableWL.CellularCatalog

end OAI
