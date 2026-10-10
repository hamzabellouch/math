import OAI.Combinatorics.VariableWL.MatrixOutput

namespace OAI

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def maximum (P Q : Expr n) : Expr n := choose (le P Q) Q P
@[simp] theorem maximum_number (P Q : Expr n) (v : Env n) : (maximum P Q).number v=max (P.number v) (Q.number v) := by
  rw [maximum,NumericProgram.choose_number,le_bit]
  by_cases h : P.number v≤Q.number v
  · simp only [decide_eq_true h,ite_true,max_eq_right h]
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,max_eq_left (Nat.le_of_not_ge h)]

def rawDimension (W C : Expr n) : Expr n := integerNumber (dimensionWord W C) C
def parsedData (W C : Expr n) : NumericProgram.Data n := {
  leftOrder := integerNumber W C
  rightOrder := integerNumber (secondWord W C) C
  dimension := minimum (rawDimension W C) (maximum (numeral 2) (integerNumber W C))
  leftMatrix := graphMatrix W C
  rightMatrix := graphMatrix (secondWord W C) C
  capacity := C }

def StrongEnough (W C : Expr n) (v : Env n) : Prop := 2^(((W.value v).length+2)^2+1)≤C.number v

theorem strong_enough (W C : Expr n) (v : Env n) (h : StrongEnough W C v) : Enough W C v := by
  apply (Nat.pow_le_pow_right (by omega : 0<2) (show (W.value v).length≤((W.value v).length+2)^2+1 by nlinarith)).trans h

theorem parsed_eval (W C : Expr n) (v : Env n) (G H : Graph) (k : ℕ)
    (hc : Enough W C v) (hp : Encoding.pair (W.value v)=some (G,H,k)) :
    (parsedData W C).eval v=NumericRefinement.data G H (InputDecision.capped G k) := by
  obtain ⟨_,hGn,hGm,hHn,hHm,hk⟩ := (pair_success W C v G H k hc).mp hp
  unfold parsedData NumericProgram.Data.eval
  rw [minimum_number,maximum_number,numeral_number]
  change NumericRefinement.Data.mk ((integerNumber W C).number v) ((integerNumber (secondWord W C) C).number v)
    (min ((rawDimension W C).number v) (max 2 ((integerNumber W C).number v)))
    ((graphMatrix W C).value v) ((graphMatrix (secondWord W C) C).value v)=_
  change k=(rawDimension W C).number v at hk
  rw [← hGn,← hGm,← hHn,← hHm,← hk]
  rfl

theorem parsed_good (W C : Expr n) (v : Env n) (G H : Graph) (k : ℕ)
    (hc : StrongEnough W C v) (hp : Encoding.pair (W.value v)=some (G,H,k)) :
    (parsedData W C).Good v := by
  obtain ⟨_,hGn,_,hHn,_,hk⟩ := (pair_success W C v G H k (strong_enough W C v hc)).mp hp
  have hcount := (RefinementSize.capped_count_bound hp).trans hc
  have h1 : 1≤C.number v := (Nat.succ_le_of_lt (pow_pos (by omega : 0<2) _)).trans hc
  change k=(rawDimension W C).number v at hk
  simp only [NumericProgram.Data.Good,parsedData,minimum_number,maximum_number,numeral_number]
  rw [← hGn,← hHn,← hk]
  change 1≤C.number v ∧ G.order^InputDecision.capped G k≤C.number v ∧ H.order^InputDecision.capped G k≤C.number v
  unfold RefinementArray.count at hcount
  exact ⟨h1,by omega,by omega⟩

def generalProgram (W C : Expr n) : Expr n :=
  conj (pairValid W C) (conj (le (numeral 2) (rawDimension W C)) (parsedData W C).accepts)

theorem generalProgram_correct (W C : Expr n) (v : Env n) (hc : StrongEnough W C v) :
    (generalProgram W C).bit v=true ↔ W.value v ∈ WL := by
  have hc' := strong_enough W C v hc
  cases hp : Encoding.pair (W.value v) with
  | none =>
    have hf : (pairValid W C).bit v≠true := by
      intro h
      obtain ⟨G,H,k,h⟩ := (pairValid_exists W C v hc').mp h
      rw [hp] at h
      contradiction
    rw [generalProgram,conj_bit,Bool.and_eq_true]
    constructor
    · rintro ⟨h,_⟩; exact (hf h).elim
    · intro h; exact (Encoding.malformed_not_WL hp h).elim
  | some q =>
    rcases q with ⟨G,H,k⟩
    obtain ⟨hv,_,_,_,_,hk⟩ := (pair_success W C v G H k hc').mp hp
    change k=(rawDimension W C).number v at hk
    have hgood := parsed_good W C v G H k hc hp
    have heval := parsed_eval W C v G H k hc' hp
    have he : (parsedData W C).accepts.bit v=true ↔ Equivalent G H (InputDecision.capped G k) := by
      unfold Expr.bit
      rw [NumericProgram.accepts_value _ _ hgood,heval]
      simp only [List.head?_cons,Option.some.injEq,decide_bool]
      exact NumericRefinement.accepts_correct G H (InputDecision.capped G k)
    simp only [generalProgram,conj_bit,Bool.and_eq_true,hv,true_and]
    rw [le_bit,numeral_number,← hk,decide_eq_true_eq,he,Encoding.pair_sound hp,Encoding.pair_mem_WL]
    exact and_congr_right fun h => (InputDecision.equivalent_capped G H h).symm

theorem generalProgram_value (W C : Expr n) (v : Env n) :
    (generalProgram W C).value v=[(generalProgram W C).bit v] := by
  simp only [generalProgram,conj_value,conj_bit]

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.Recipe
variable {n : ℕ}

theorem iterate_controlled {B Z : Certified n} {Q : Certified (n+2)}
    (hB : Poly B) (hZ : Poly Z) (hQ : Poly Q) :
    ∃f : ℕ → ℕ, Growth f ∧ ∀C v,EnvBound C v →
      (∀j≤(B.value v).length,(foldValue Q v (Z.value v) j).length≤C) →
      (iterate B Z Q).time v+((iterate B Z Q).value v).length≤f C := by
  obtain ⟨b,hb,hB⟩ := hB
  obtain ⟨z,hz,hZ⟩ := hZ
  obtain ⟨q,hq,hQ⟩ := hQ
  let D : ℕ → ℕ := fun C=>b C+C+C
  have hD : Growth D := (hb.add Growth.ident).add Growth.ident
  refine ⟨fun C=>13*(b C+z C+C)+(q (D C)+3*C+6)*b C+24,?_,?_⟩
  · exact (((Growth.constant 13).mul ((hb.add hz).add Growth.ident)).add
      ((((hq.comp hD).add ((Growth.constant 3).mul Growth.ident)).add (Growth.constant 6)).mul hb)).add (Growth.constant 24)
  · intro C v hv hacc
    have h1 := hB C v hv
    have h2 := hZ C v hv
    have h3 := hacc (B.value v).length le_rfl
    have hcost (j : ℕ) (hj : j<(B.value v).length) : foldTime Q v (Z.value v) j≤q (D C)+3*C+2 := by
      have h4 := hacc j (by omega)
      have hev : EnvBound (D C) (cons (foldValue Q v (Z.value v) j) (cons (List.replicate j true) v)) := by
        apply envBound_cons
        · apply envBound_cons
          · intro i; have := hv i; dsimp only [D]; omega
          · simp only [List.length_replicate]; dsimp only [D]; omega
        · dsimp only [D]; omega
      have h5 := hQ (D C) _ hev
      unfold foldTime
      omega
    have htot := BoundedLoop.total_bound (B.value v).length (q (D C)+3*C+2) _ hcost
    have htot' : BoundedLoop.total (B.value v).length (foldTime Q v (Z.value v))≤
        (q (D C)+3*C+6)*b C := by
      apply htot.trans
      have hm := Nat.mul_le_mul_left (q (D C)+3*C+6) (show (B.value v).length≤b C by omega)
      simpa only [Nat.add_assoc] using hm
    rw [iterate_time,iterate_value]
    dsimp only
    omega

theorem power_prefix (B : Certified n) (v : Env n) (j : ℕ) :
    foldValue (times (input 0) (B.reindex (fun i=>i.succ.succ))) v [true] j=
      List.replicate ((B.value v).length^j) true := by
  have h := power_value B (literal (List.replicate j true)) v
  rw [power,iterate_value] at h
  simpa only [literal_value,List.length_replicate] using h

theorem outputs (P : Certified 1) : ∃M : VariableWL.Machine,∀w : Word,
    OutputsWithin M w (P.value (fun _=>w.reverse)) (4*(w.length+P.time (fun _=>w.reverse)+1)) := by
  obtain ⟨M,hM⟩ := Procedure.outputs (1 : Fin 2) (P.compiled 1 (fun _=>0) 1)
  refine ⟨M,fun w=>?_⟩
  have h := hM w
  have he : (fun j : Fin 2=>if j=0 then w.reverse else []) ∘ (fun _ : Fin 1=>(0 : Fin 2))=(fun _=>w.reverse) := rfl
  simp only [Function.update_self,he,show (1 : Fin 2)≠0 by decide,ite_false,List.length_nil,Nat.mul_zero,Nat.add_zero] at h
  exact h

end VariableWL.Computation.Stack.Recipe

namespace VariableWL.Computation.Stack.ExponentialRecipe
open Recipe PolyRecipe

def exponent : Expr 1 :=
  add (mul (add (length (PolyRecipe.input 0)) (numeral 2)) (add (length (PolyRecipe.input 0)) (numeral 2))) (numeral 1)
def size (v : Env 1) : ℕ := 2^(((v 0).length+2)^2+1)
def capacity : Certified 1 := Recipe.power (Recipe.literal [true,true]) exponent.program

theorem exponent_number (v : Env 1) : exponent.number v=((v 0).length+2)^2+1 := by
  simp only [exponent,add_number,mul_number,length_number,PolyRecipe.input_value,numeral_number,pow_two]

theorem capacity_value (v : Env 1) : capacity.value v=List.replicate (size v) true := by
  rw [capacity,Recipe.power_value]
  change List.replicate (2^exponent.number v) true=_
  rw [exponent_number]
  rfl

theorem input_le_size (v : Env 1) : (v 0).length≤ size v := by
  have hh := Nat.lt_two_pow_self (n := ((v 0).length+2)^2+1)
  unfold size
  nlinarith

theorem envBound_size (v : Env 1) : EnvBound (size v) v := by
  intro i
  have hi : i=0 := Fin.eq_zero i
  subst i
  exact input_le_size v

theorem capacity_cost : ∃f : ℕ → ℕ,Growth f ∧ ∀v,capacity.time v+(capacity.value v).length≤f (size v) := by
  obtain ⟨f,hf,h⟩ := Recipe.iterate_controlled exponent.polynomial (poly_literal [true])
    (poly_times (poly_input (0 : Fin 3)) (poly_reindex (poly_literal [true,true]) (fun i : Fin 1=>i.succ.succ)))
  refine ⟨f,hf,fun v=>h (size v) v (envBound_size v) ?_⟩
  intro j hj
  rw [Recipe.literal_value,Recipe.power_prefix,Recipe.literal_value,List.length_replicate]
  change 2^j≤ size v
  apply Nat.pow_le_pow_right (by omega)
  change j≤exponent.number v at hj
  rw [exponent_number] at hj
  exact hj

def full (Q : Expr 2) : Certified 1 := capacity.bind Q.program

theorem full_value (Q : Expr 2) (v : Env 1) :
    (full Q).value v=Q.value (cons (List.replicate (size v) true) v) := by
  change Q.value (cons (capacity.value v) v)=_
  rw [capacity_value]

theorem full_cost (Q : Expr 2) : ∃f : ℕ → ℕ,Growth f ∧ ∀v,(full Q).time v≤f (size v) := by
  obtain ⟨a,ha,hA⟩ := capacity_cost
  obtain ⟨b,hb,hB⟩ := Q.polynomial
  refine ⟨fun C=>a C+b C+3*C+2,((ha.add hb).add ((Growth.constant 3).mul Growth.ident)).add (Growth.constant 2),?_⟩
  intro v
  have hbv : EnvBound (size v) (cons (capacity.value v) v) :=
    envBound_cons (envBound_size v) (by rw [capacity_value,List.length_replicate])
  have ht := hB (size v) _ hbv
  have hc := hA v
  change capacity.time v+Q.program.time (cons (capacity.value v) v)+3*(capacity.value v).length+2≤_
  simp only [capacity_value,List.length_replicate] at hc ht ⊢
  omega

def environment (w : Word) : Env 2 := cons (List.replicate (2^((w.length+2)^2+1)) true) (fun _=>w.reverse)

theorem inEXPTIME (Q : Expr 2) (L : Language)
    (hword : ∀w,Q.value (environment w)=[Q.bit (environment w)])
    (hcorrect : ∀w,Q.bit (environment w)=true ↔ w∈L) : InEXPTIME L := by
  obtain ⟨M,hM⟩ := Recipe.outputs (full Q)
  obtain ⟨f,hf,hF⟩ := full_cost Q
  let g : ℕ → ℕ := fun C=>4*(C+f C+1)
  have hg : Growth g := (Growth.constant 4).mul ((Growth.ident.add hf).add (Growth.constant 1))
  obtain ⟨c,d,hg⟩ := hg
  refine ⟨M,16*(c+d+1),2,fun w=>⟨Q.bit (environment w),hcorrect w,?_⟩⟩
  have hm := hM w
  rw [full_value] at hm
  have hs : size (fun _ : Fin 1=>w.reverse)=2^((w.length+2)^2+1) := by simp only [size,List.length_reverse]
  rw [hs] at hm
  change OutputsWithin M w (Q.value (environment w)) _ at hm
  rw [hword] at hm
  have htime := hF (fun _ : Fin 1=>w.reverse)
  have hlen := input_le_size (fun _ : Fin 1=>w.reverse)
  rw [List.length_reverse] at hlen
  have hbound : 4*(w.length+(full Q).time (fun _=>w.reverse)+1)≤g (size (fun _ : Fin 1=>w.reverse)) := by
    dsimp only [g]
    omega
  have hp := RefinementSize.polynomial_of_exponential c d (w.length+2) (size (fun _ : Fin 1=>w.reverse))
    (by rw [hs,pow_two])
  have hfinal : (c+d+1)*(w.length+2+2)^2≤(16*(c+d+1))*(w.length+1)^2 := by
    have hb : w.length+2+2≤4*(w.length+1) := by omega
    have hh := Nat.pow_le_pow_left hb 2
    have hm := Nat.mul_le_mul_left (c+d+1) hh
    nlinarith
  obtain ⟨t,ht,hhalt,hout⟩ := hm
  exact ⟨t,ht.trans (hbound.trans ((hg _).trans (hp.trans (Nat.pow_le_pow_right (by omega) hfinal)))),hhalt,hout⟩

end VariableWL.Computation.Stack.ExponentialRecipe

namespace VariableWL.Computation.Stack.ExponentialRecipe
open Recipe PolyRecipe

def general : Expr 2 := generalProgram (PolyRecipe.reverse (PolyRecipe.input 1)) (PolyRecipe.input 0)

theorem general_upper : InEXPTIME WL := by
  apply inEXPTIME general WL
  · intro w; exact generalProgram_value _ _ _
  · intro w
    have hv : (PolyRecipe.reverse (PolyRecipe.input (1 : Fin 2))).value (environment w)=w := by
      change w.reverse.reverse=w
      exact List.reverse_reverse w
    have hc : StrongEnough (PolyRecipe.reverse (PolyRecipe.input 1)) (PolyRecipe.input 0) (environment w) := by
      unfold StrongEnough
      rw [hv,input_number]
      simp only [environment,cons_zero,List.length_replicate]
      exact le_rfl
    have h := generalProgram_correct _ _ _ hc
    rw [hv] at h
    exact h

end VariableWL.Computation.Stack.ExponentialRecipe

namespace VariableWL.NumericPromise
attribute [local instance] Classical.propDecidable

def get (n : ℕ) (R : Word) (a b : ℕ) : Bool := R.getD (a*n+b) false
def pack (n : ℕ) (f : ℕ → ℕ → Bool) : Word :=
  (List.range (n*n)).map fun p=>f (p/n) (p%n)
def update (n : ℕ) (A R : Word) (a b : ℕ) : Bool :=
  get n R a b || (List.range n).any fun z=>get n A a z && get n R z b
def array (n : ℕ) (A : Word) : ℕ → Word
  | 0 => pack n (fun a b=>decide (a=b))
  | j+1 => pack n (update n A (array n A j))

theorem get_pack (n : ℕ) (f : ℕ → ℕ → Bool) (a b : Fin n) :
    get n (pack n f) a b=f a b := by
  have hn : 0<n := Nat.zero_lt_of_lt a.isLt
  have hp : a.val*n+b.val<n*n := by
    have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt a.isLt)
    nlinarith [b.isLt]
  unfold get pack
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map,List.length_range] using hp)]
  simp only [List.getElem_map,List.getElem_range]
  have hd : (a.val*n+b.val)/n=a.val := by
    rw [Nat.mul_comm a.val n,Nat.mul_add_div hn,Nat.div_eq_of_lt b.isLt,Nat.add_zero]
  rw [hd]
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt b.isLt]

theorem get_matrix (G : Graph) (a b : Fin G.order) :
    get G.order (Encoding.matrix G) a b=decide (G.graph.Adj a b) := Encoding.entry_matrix G a b

theorem array_correct (G : Graph) (j : ℕ) (a b : Fin G.order) :
    get G.order (array G.order (Encoding.matrix G) j) a b=PromiseDecision.reach G j a b := by
  induction j generalizing a b with
  | zero =>
    rw [array,get_pack,PromiseDecision.reach]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,Fin.val_inj]
  | succ j ih =>
    rw [array,get_pack,update,ih,PromiseDecision.reach]
    congr 1
    rw [← List.map_coe_finRange_eq_range,List.any_map]
    apply congrArg (fun p : Fin G.order → Bool=>(List.finRange G.order).any p)
    funext z
    dsimp only [Function.comp_def]
    rw [get_matrix,ih]

def connected (n : ℕ) (A : Word) : Bool := decide (0<n) &&
  (List.range n).all fun a=>(List.range n).all fun b=>get n (array n A n) a b

def subcubic (n : ℕ) (A : Word) : Bool :=
  (List.range n).all fun a=>decide ((List.range n).countP (fun b=>get n A a b)≤3)

theorem connected_correct (G : Graph) : connected G.order (Encoding.matrix G)=PromiseDecision.connected G := by
  unfold connected PromiseDecision.connected
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.all_map,Function.comp_def,array_correct]

theorem subcubic_correct (G : Graph) : subcubic G.order (Encoding.matrix G)=PromiseDecision.subcubic G := by
  unfold subcubic PromiseDecision.subcubic PromiseDecision.neighbors
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.all_map,List.filter_map,Function.comp_def,get_matrix,List.length_map,List.countP_eq_length_filter]

end VariableWL.NumericPromise

end OAI
