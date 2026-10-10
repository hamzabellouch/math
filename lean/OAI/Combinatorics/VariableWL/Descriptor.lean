import OAI.Combinatorics.VariableWL.ExponentialRecipe

namespace OAI

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def any (N : Expr n) (B : Expr (n+1)) : Expr n := neg (all N (neg B))
@[simp] theorem any_bit (N : Expr n) (B : Expr (n+1)) (v : Env n) :
    (any N B).bit v=(List.range (N.number v)).any fun j=>B.bit (cons (List.replicate j true) v) := by
  simp only [any,neg_bit,all_bit,List.any_eq_not_all_not]

def reachInitial (N : Expr n) : Expr n :=
  collect (mul N N) (eq (div (input 0) N.up) (mod (input 0) N.up))
def reachUpdate (N A R I J : Expr n) : Expr n :=
  disj (matrixEntry R N I J) (any N (conj (matrixEntry A.up N.up I.up (input 0))
    (matrixEntry R.up N.up (input 0) J.up)))
def reachNext (N A R : Expr n) : Expr n :=
  collect (mul N N) (reachUpdate N.up A.up R.up (div (input 0) N.up) (mod (input 0) N.up))

theorem reachInitial_value (N : Expr n) (v : Env n) :
    (reachInitial N).value v=NumericPromise.array (N.number v) [] 0 := by
  simp only [reachInitial,collect_value,mul_number,eq_bit,div_number,mod_number,input_number,
    cons_zero,List.length_replicate,up_number]
  rfl

theorem reachUpdate_bit (N A R I J : Expr n) (v : Env n) :
    (reachUpdate N A R I J).bit v=NumericPromise.update (N.number v) (A.value v) (R.value v) (I.number v) (J.number v) := by
  simp only [reachUpdate,disj_bit,matrixEntry_bit,any_bit,conj_bit,up_value,up_number,input_number,cons_zero,List.length_replicate]
  rfl

theorem reachNext_value (N A R : Expr n) (v : Env n) :
    (reachNext N A R).value v=NumericPromise.pack (N.number v)
      (NumericPromise.update (N.number v) (A.value v) (R.value v)) := by
  simp only [reachNext,collect_value,mul_number,reachUpdate_bit,up_number,up_value,div_number,mod_number,
    input_number,cons_zero,List.length_replicate]
  rfl

theorem reachInitial_length (N : Expr n) (v : Env n) : ((reachInitial N).value v).length=N.number v^2 := by
  rw [reachInitial_value]
  simp only [NumericPromise.array,NumericPromise.pack,List.length_map,List.length_range,pow_two]

theorem reachNext_length (N A R : Expr n) (v : Env n) : ((reachNext N A R).value v).length=N.number v^2 := by
  rw [reachNext_value]
  simp only [NumericPromise.pack,List.length_map,List.length_range,pow_two]

def reachBody (N A : Expr n) : Expr (n+2) := reachNext N.up₂ A.up₂ (input 0)
def reachProgram (N A : Expr n) : Certified n :=
  Recipe.iterate N.program (reachInitial N).program (reachBody N A).program

theorem reachPrefix_length (N A : Expr n) (v : Env n) (j : ℕ) :
    (Recipe.foldValue (reachBody N A).program v ((reachInitial N).value v) j).length=N.number v^2 := by
  cases j with
  | zero => exact reachInitial_length N v
  | succ j =>
    change ((reachNext N.up₂ A.up₂ (input 0)).value _).length=_
    rw [reachNext_length,up₂_number]

theorem reachProgram_poly (N A : Expr n) : Poly (reachProgram N A) := by
  obtain ⟨f,hf,h⟩ := N.polynomial
  apply Recipe.poly_iterate N.polynomial (reachInitial N).polynomial (reachBody N A).polynomial
    (fun C=>(f C)^2) (hf.pow 2)
  intro C v hv j hj
  change (Recipe.foldValue (reachBody N A).program v ((reachInitial N).value v) j).length≤(f C)^2
  rw [reachPrefix_length]
  have hb := h C v hv
  exact Nat.pow_le_pow_left (show N.number v≤f C by exact (Nat.le_add_left _ _).trans hb) 2

def reachArray (N A : Expr n) : Expr n := ⟨reachProgram N A,reachProgram_poly N A⟩

theorem reachPrefix_value (N A : Expr n) (v : Env n) (j : ℕ) :
    Recipe.foldValue (reachBody N A).program v ((reachInitial N).value v) j=
      NumericPromise.array (N.number v) (A.value v) j := by
  induction j with
  | zero => exact reachInitial_value N v
  | succ j ih =>
    change (reachNext N.up₂ A.up₂ (input 0)).value _=_
    rw [reachNext_value]
    simp only [up₂_number,up₂_value,input_value,cons_zero,ih]
    rfl

theorem reachArray_value (N A : Expr n) (v : Env n) :
    (reachArray N A).value v=NumericPromise.array (N.number v) (A.value v) (N.number v) := by
  change (Recipe.iterate N.program (reachInitial N).program (reachBody N A).program).value v=_
  rw [Recipe.iterate_value]
  exact reachPrefix_value N A v (N.number v)

def connectedProgram (N A : Expr n) : Expr n :=
  conj (lt (numeral 0) N) (all N (all N.up (matrixEntry (reachArray N A).up₂ N.up₂ (input 1) (input 0))))
def subcubicProgram (N A : Expr n) : Expr n :=
  all N (le (count N.up (matrixEntry A.up₂ N.up₂ (input 1) (input 0))) (numeral 3))

theorem connectedProgram_bit (N A : Expr n) (v : Env n) :
    (connectedProgram N A).bit v=NumericPromise.connected (N.number v) (A.value v) := by
  simp only [connectedProgram,conj_bit,lt_bit,numeral_number,all_bit,matrixEntry_bit,up_number,up₂_number,
    up₂_value,reachArray_value,input_number,NumericProgram.cons_one,cons_zero,List.length_replicate]
  rfl

theorem subcubicProgram_bit (N A : Expr n) (v : Env n) :
    (subcubicProgram N A).bit v=NumericPromise.subcubic (N.number v) (A.value v) := by
  simp only [subcubicProgram,all_bit,le_bit,count_number,matrixEntry_bit,up_number,up₂_number,
    up₂_value,numeral_number,input_number,NumericProgram.cons_one,cons_zero,List.length_replicate]
  rfl

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def promiseProgram (N M A B : Expr n) : Expr n :=
  conj (lt (numeral 0) N) (conj (eq N M) (conj (connectedProgram N A)
    (conj (connectedProgram M B) (conj (subcubicProgram N A) (subcubicProgram M B)))))

theorem promiseProgram_correct (N M A B : Expr n) (v : Env n) (G H : Graph)
    (hN : N.number v=G.order) (hM : M.number v=H.order)
    (hA : A.value v=Encoding.matrix G) (hB : B.value v=Encoding.matrix H) :
    (promiseProgram N M A B).bit v=true ↔
      0<G.order ∧ G.order=H.order ∧ G.graph.Connected ∧ H.graph.Connected ∧ Subcubic G ∧ Subcubic H := by
  simp only [promiseProgram,conj_bit,Bool.and_eq_true,lt_bit,eq_bit,numeral_number,
    connectedProgram_bit,subcubicProgram_bit,hN,hM,hA,hB,decide_eq_true_eq,
    NumericPromise.connected_correct,NumericPromise.subcubic_correct,
    PromiseDecision.connected_correct,PromiseDecision.subcubic_correct]

def subProgram (W C : Expr n) : Expr n :=
  conj (generalProgram W C) (promiseProgram (integerNumber W C) (integerNumber (secondWord W C) C)
    (graphMatrix W C) (graphMatrix (secondWord W C) C))

theorem subProgram_correct (W C : Expr n) (v : Env n) (hc : StrongEnough W C v) :
    (subProgram W C).bit v=true ↔ W.value v∈SubWL := by
  have hg := generalProgram_correct W C v hc
  cases hp : Encoding.pair (W.value v) with
  | none =>
    rw [subProgram,conj_bit,Bool.and_eq_true,hg]
    constructor
    · rintro ⟨h,_⟩; exact (Encoding.malformed_not_WL hp h).elim
    · intro h; exact (Encoding.malformed_not_SubWL hp h).elim
  | some q =>
    rcases q with ⟨G,H,k⟩
    obtain ⟨_,hGn,hGm,hHn,hHm,_⟩ := (pair_success W C v G H k (strong_enough W C v hc)).mp hp
    have hpromise := promiseProgram_correct (integerNumber W C) (integerNumber (secondWord W C) C)
      (graphMatrix W C) (graphMatrix (secondWord W C) C) v G H hGn.symm hHn.symm hGm.symm hHm.symm
    rw [subProgram,conj_bit,Bool.and_eq_true,hg,hpromise,Encoding.pair_sound hp,
      Encoding.pair_mem_WL,Encoding.pair_mem_SubWL]
    constructor
    · rintro ⟨⟨h₁,h₈⟩,h₂,h₃,h₄,h₅,h₆,h₇⟩
      exact ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈⟩
    · rintro ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈⟩
      exact ⟨⟨h₁,h₈⟩,h₂,h₃,h₄,h₅,h₆,h₇⟩

theorem subProgram_value (W C : Expr n) (v : Env n) :
    (subProgram W C).value v=[(subProgram W C).bit v] := by
  simp only [subProgram,conj_value,conj_bit]

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.ExponentialRecipe
open Recipe PolyRecipe

def subcubic : Expr 2 := subProgram (PolyRecipe.reverse (PolyRecipe.input 1)) (PolyRecipe.input 0)

theorem subcubic_upper : InEXPTIME SubWL := by
  apply inEXPTIME subcubic SubWL
  · intro w; exact subProgram_value _ _ _
  · intro w
    have hv : (PolyRecipe.reverse (PolyRecipe.input (1 : Fin 2))).value (environment w)=w := by
      change w.reverse.reverse=w
      exact List.reverse_reverse w
    have hc : StrongEnough (PolyRecipe.reverse (PolyRecipe.input 1)) (PolyRecipe.input 0) (environment w) := by
      unfold StrongEnough
      rw [hv,input_number]
      simp only [environment,cons_zero,List.length_replicate]
      exact le_rfl
    have h := subProgram_correct _ _ _ hc
    rw [hv] at h
    exact h

end VariableWL.Computation.Stack.ExponentialRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def binaryLength (N : Expr n) : Expr n :=
  count N (le (capPow (numeral 2) (input 0) (add N.up (numeral 1))) N.up)

theorem binaryLength_number (N : Expr n) (v : Env n) : (binaryLength N).number v=(N.number v).size := by
  rw [binaryLength,count_number]
  simp only [le_bit,capPow_number,numeral_number,input_number,cons_zero,List.length_replicate,add_number,up_number]
  have he (j : ℕ) : decide (min (2^j) (N.number v+1)≤N.number v)=decide (j<(N.number v).size) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,Nat.lt_size]
    omega
  simp only [he]
  rw [Recipe.count_range_lt,Nat.min_eq_right]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

def binaryDigit (N I : Expr n) : Expr n :=
  eq (mod (div N (capPow (numeral 2) I (add N (numeral 1)))) (numeral 2)) (numeral 1)

theorem binaryDigit_bit (N I : Expr n) (v : Env n) (h : I.number v<(N.number v).size) :
    (binaryDigit N I).bit v=(N.number v).testBit (I.number v) := by
  have hp := Nat.lt_size.mp h
  rw [binaryDigit,eq_bit,mod_number,div_number,capPow_number,add_number]
  simp only [numeral_number,Nat.min_eq_left (show 2^I.number v≤N.number v+1 by omega)]
  exact Nat.testBit_eq_decide_div_mod_eq.symm

def binaryEncode (N : Expr n) : Expr n := collect (binaryLength N) (binaryDigit N.up (input 0))

theorem binaryEncode_value (N : Expr n) (v : Env n) : (binaryEncode N).value v=(N.number v).bits := by
  rw [binaryEncode,collect_value,binaryLength_number]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,Nat.size_eq_bits_len]
  · intro i hi hi'
    rw [List.getElem_map,List.getElem_range]
    have h : (input (0 : Fin (n+1))).number (cons (List.replicate i true) v)<(N.up.number (cons (List.replicate i true) v)).size := by
      simpa only [input_number,cons_zero,List.length_replicate,up_number,List.length_map,List.length_range] using hi
    rw [binaryDigit_bit _ _ _ h]
    simp only [up_number,input_number,cons_zero,List.length_replicate,Nat.testBit_eq_inth,List.getI_eq_getElem _ hi']

def integerEncode (N : Expr n) : Expr n :=
  append (length (binaryEncode N)) (append (literal [false]) (binaryEncode N))

theorem integerEncode_value (N : Expr n) (v : Env n) : (integerEncode N).value v=integerCode (N.number v) := by
  simp only [integerEncode,append_value,literal_value]
  change List.replicate ((binaryEncode N).value v).length true ++ ([false] ++ (binaryEncode N).value v)=_
  rw [binaryEncode_value]
  exact List.append_assoc _ _ _ |>.symm

def graphEncode (N A : Expr n) : Expr n := append (integerEncode N) A

def pairEncode (N M A B K : Expr n) : Expr n :=
  append (graphEncode N A) (append (graphEncode M B) (integerEncode K))

theorem graphEncode_value (N A : Expr n) (v : Env n) (G : Graph)
    (hn : N.number v=G.order) (ha : A.value v=Encoding.matrix G) :
    (graphEncode N A).value v=graphCode G := by
  rw [graphEncode,append_value,integerEncode_value,hn,ha,Encoding.graphCode_eq]

theorem pairEncode_value (N M A B K : Expr n) (v : Env n) (G H : Graph) (k : ℕ)
    (hn : N.number v=G.order) (hm : M.number v=H.order) (ha : A.value v=Encoding.matrix G)
    (hb : B.value v=Encoding.matrix H) (hk : K.number v=k) :
    (pairEncode N M A B K).value v=pairCode G H k := by
  rw [pairEncode,append_value,append_value,graphEncode_value _ _ _ _ hn ha,
    graphEncode_value _ _ _ _ hm hb,integerEncode_value,hk]
  exact List.append_assoc _ _ _ |>.symm

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Descriptor

def rank (P : ℕ → Bool) (a : ℕ) : ℕ := (List.range a).countP P

theorem rank_succ (P : ℕ → Bool) (a : ℕ) :
    rank P (a+1)=rank P a+(if P a then 1 else 0) := by
  simp only [rank,List.range_succ,List.countP_append,List.countP_cons,List.countP_nil,Nat.zero_add]

theorem rank_mono (P : ℕ → Bool) : Monotone (rank P) := by
  intro a b h
  exact List.Sublist.countP_le (List.range_sublist.mpr h)

theorem rank_lt (P : ℕ → Bool) {a b : ℕ} (h : a<b) (ha : P a=true) : rank P a<rank P b := by
  have hm := rank_mono P (Nat.succ_le_of_lt h)
  simp only [rank_succ,ha,ite_true] at hm
  omega

theorem rank_exists (P : ℕ → Bool) (N i : ℕ) (hi : i<rank P N) :
    ∃a,a<N ∧ P a=true ∧ rank P a=i := by
  induction N with
  | zero => simp [rank] at hi
  | succ N ih =>
    by_cases h : i<rank P N
    · obtain ⟨a,ha,hp,hr⟩ := ih h
      exact ⟨a,by omega,hp,hr⟩
    · rw [rank_succ] at hi
      cases hp : P N <;> simp only [hp,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at hi
      · omega
      · exact ⟨N,by omega,hp,by omega⟩

def pick (N : ℕ) (P : ℕ → Bool) (i : ℕ) : ℕ :=
  (List.range N).countP fun j=>decide (rank P (j+1)≤ i)

theorem pick_rank (N : ℕ) (P : ℕ → Bool) (a : ℕ) (ha : a<N) (hp : P a=true) :
    pick N P (rank P a)=a := by
  have he (j : ℕ) : decide (rank P (j+1)≤rank P a)=decide (j<a) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      by_contra hj
      have hm := rank_lt P (show a<j+1 by omega) hp
      omega
    · exact fun h=>rank_mono P (Nat.succ_le_of_lt h)
  simp only [pick,he]
  rw [Computation.Stack.Recipe.count_range_lt,Nat.min_eq_right (Nat.le_of_lt ha)]

theorem pick_spec (N : ℕ) (P : ℕ → Bool) (i : ℕ) (hi : i<rank P N) :
    pick N P i<N ∧ P (pick N P i)=true ∧ rank P (pick N P i)=i := by
  obtain ⟨a,ha,hp,hr⟩ := rank_exists P N i hi
  rw [←hr,pick_rank N P a ha hp]
  exact ⟨ha,hp,rfl⟩

abbrev Valid (N : ℕ) (P : ℕ → Bool) := {a : Fin N // P a.val=true}

def rankEquiv (N : ℕ) (P : ℕ → Bool) : Valid N P ≃ Fin (rank P N) where
  toFun a := ⟨rank P a.val.val,rank_lt P a.val.isLt a.property⟩
  invFun i := ⟨⟨pick N P i.val,(pick_spec N P i.val i.isLt).1⟩,(pick_spec N P i.val i.isLt).2.1⟩
  left_inv a := by apply Subtype.ext; apply Fin.ext; exact pick_rank N P a.val.val a.val.isLt a.property
  right_inv i := by apply Fin.ext; exact (pick_spec N P i.val i.isLt).2.2

end VariableWL.Descriptor

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def underOne (P : Expr (n+1)) : Expr (n+2) := P.reindex (Fin.cons 0 (fun i=>i.succ.succ))

theorem underOne_value (P : Expr (n+1)) (v : Env n) (a b : Word) :
    (underOne P).value (cons a (cons b v))=P.value (cons a v) := by
  apply congrArg P.program.value
  funext i
  exact Fin.cases rfl (fun _=>rfl) i

theorem underOne_bit (P : Expr (n+1)) (v : Env n) (a b : Word) :
    (underOne P).bit (cons a (cons b v))=P.bit (cons a v) := by
  unfold Expr.bit
  rw [underOne_value]

def select (N : Expr n) (P : Expr (n+1)) (I : Expr n) : Expr n :=
  count N (le (count (add (input 0) (numeral 1)) (underOne P)) I.up)

theorem select_number (N : Expr n) (P : Expr (n+1)) (I : Expr n) (v : Env n) :
    (select N P I).number v=Descriptor.pick (N.number v)
      (fun j=>P.bit (cons (List.replicate j true) v)) (I.number v) := by
  simp only [select,count_number,le_bit,add_number,input_number,cons_zero,List.length_replicate,
    numeral_number,underOne_bit,up_number]
  rfl

def apply₂ (F : Expr (n+2)) (A B : Expr n) : Expr n := B.bind (A.up.bind F)

theorem apply₂_value (F : Expr (n+2)) (A B : Expr n) (v : Env n) :
    (apply₂ F A B).value v=F.value (cons (A.value v) (cons (B.value v) v)) := by
  simp only [apply₂,bind_value,up_value]

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Descriptor
attribute [local instance] Classical.propDecidable

structure Data where
  bound : ℕ
  valid : ℕ → Bool
  edge : ℕ → ℕ → Bool

def Data.Sound (D : Data) : Prop :=
  (∀a b,a<D.bound → b<D.bound → D.valid a=true → D.valid b=true → D.edge a b=D.edge b a) ∧
  (∀a,a<D.bound → D.valid a=true → D.edge a a=false)

noncomputable def Data.graph (D : Data) (h : D.Sound) : Graph where
  order := rank D.valid D.bound
  graph := {
    Adj := fun i j=>D.edge (pick D.bound D.valid i.val) (pick D.bound D.valid j.val)=true
    symm := ⟨by
      intro i j hij
      have hi := pick_spec D.bound D.valid i.val i.isLt
      have hj := pick_spec D.bound D.valid j.val j.isLt
      rw [h.1 _ _ hj.1 hi.1 hj.2.1 hi.2.1]
      exact hij⟩
    loopless := ⟨by
      intro i he
      have hi := pick_spec D.bound D.valid i.val i.isLt
      rw [h.2 _ hi.1 hi.2.1] at he
      contradiction⟩ }

noncomputable def Data.iso (D : Data) (h : D.Sound) (G : Graph)
    (e : Valid D.bound D.valid ≃ Fin G.order)
    (he : ∀a b,D.edge a.val.val b.val.val=true ↔ G.graph.Adj (e a) (e b)) :
    (D.graph h).graph ≃g G.graph where
  toEquiv := (rankEquiv D.bound D.valid).symm.trans e
  map_rel_iff' := by
    intro i j
    exact (he ((rankEquiv D.bound D.valid).symm i) ((rankEquiv D.bound D.valid).symm j)).symm

end VariableWL.Descriptor

end OAI
