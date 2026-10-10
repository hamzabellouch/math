import OAI.Combinatorics.VariableWL.NumericProgram

namespace OAI

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

@[simp] theorem input_one_bit (a : Word) (b : Bool) (v : Env n) :
    (input (1 : Fin (n+2))).bit (cons a (cons [b] v))=b := by cases b <;> rfl

def binaryStep (C : Expr n) : Expr (n+2) :=
  minimum (add (mul (numeral 2) (input 0)) (choose (input 1) (numeral 1) (numeral 0))) C.up₂

theorem binaryStep_value (C : Expr n) (v : Env n) (a : Word) (b : Bool) :
    (binaryStep C).value (cons a (cons [b] v))=List.replicate (min (2*a.length+b.toNat) (C.number v)) true := by
  rw [binaryStep,minimum_value,add_number,mul_number,numeral_number,input_number,cons_zero,
    NumericProgram.choose_number,input_one_bit,numeral_number,numeral_number,up₂_number]
  cases b <;> rfl

theorem min_double (q C b : ℕ) : min (2*min q C+b) C=min (2*q+b) C := by
  by_cases h : q≤C
  · rw [min_eq_left h]
  · have hq : C≤q := by omega
    rw [min_eq_right hq,min_eq_right (by omega),min_eq_right (by omega)]

theorem binary_fold (C : Expr n) (v : Env n) (w : Word) (q : ℕ) :
    w.foldl (foldWordStep (binaryStep C) v) (List.replicate (min q (C.number v)) true)=
      List.replicate (min (BinaryMachine.value w q) (C.number v)) true := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih =>
    rw [List.foldl_cons]
    unfold foldWordStep
    rw [binaryStep_value,List.length_replicate,min_double]
    exact ih (2*q+b.toNat)

theorem binary_poly (W C : Expr n) : Poly (foldWordProgram (reverse W) (numeral 0) (binaryStep C)) := by
  obtain ⟨f,hf,h⟩ := C.polynomial
  apply foldWordProgram_poly _ _ _ f hf
  intro N v hv j hj
  have h0 : (numeral (0 : ℕ) : Expr n).value v=List.replicate (min 0 (C.number v)) true := by simp [numeral]
  rw [h0,binary_fold,List.length_replicate]
  have hc := h N v hv
  exact (min_le_right _ _).trans (by exact (Nat.le_add_left _ _).trans hc)

def binary (W C : Expr n) : Expr n := ⟨foldWordProgram (reverse W) (numeral 0) (binaryStep C),binary_poly W C⟩

theorem binary_value (W C : Expr n) (v : Env n) :
    (binary W C).value v=List.replicate (min (Encoding.value (W.value v)) (C.number v)) true := by
  change (foldWordProgram (reverse W) (numeral 0) (binaryStep C)).value v=_
  rw [foldWordProgram_value,reverse_value]
  have h0 : (numeral (0 : ℕ) : Expr n).value v=List.replicate (min 0 (C.number v)) true := by simp [numeral]
  rw [h0,binary_fold,BinaryMachine.value_reverse]
  simp only [Nat.zero_mul,Nat.zero_add]

@[simp] theorem binary_number (W C : Expr n) (v : Env n) :
    (binary W C).number v=min (Encoding.value (W.value v)) (C.number v) := by
  unfold Expr.number
  rw [binary_value,List.length_replicate]
  rfl

def prefixStep : Expr (n+2) := choose (input 1) (add (input 0) (numeral 1)) (numeral 0)

def prefixValue : Word → ℕ → ℕ
  | [],q => q
  | false::w,_q => prefixValue w 0
  | true::w,q => prefixValue w (q+1)

def headCount : Word → ℕ
  | [] => 0
  | false::_ => 0
  | true::w => headCount w+1

theorem prefixValue_bound (w : Word) (q : ℕ) : prefixValue w q≤w.length+q := by
  induction w generalizing q with
  | nil => simp [prefixValue]
  | cons b w ih => cases b <;> simp only [prefixValue,List.length_cons] <;> have h := ih (q+1) <;> have h' := ih 0 <;> omega

theorem prefixValue_append (u w : Word) (q : ℕ) : prefixValue (u++w) q=prefixValue w (prefixValue u q) := by
  induction u generalizing q with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [List.cons_append,prefixValue,ih]

theorem prefixValue_reverse (w : Word) (q : ℕ) :
    prefixValue w.reverse q=headCount w+(if w.all id then q else 0) := by
  induction w with
  | nil => simp [prefixValue,headCount]
  | cons b w ih =>
    rw [List.reverse_cons,prefixValue_append]
    cases b with
    | false => simp [prefixValue,headCount]
    | true =>
      simp only [prefixValue,headCount,List.all_cons,id_eq,Bool.true_and]
      rw [ih]
      omega

theorem prefixStep_value (v : Env n) (q : ℕ) (b : Bool) :
    (prefixStep : Expr (n+2)).value (cons (List.replicate q true) (cons [b] v))=
      List.replicate (if b then q+1 else 0) true := by
  rw [prefixStep,choose_value,input_one_bit]
  cases b with
  | false => rfl
  | true =>
    change (Recipe.plus (Recipe.input 0) (Recipe.literal [true])).value (cons (List.replicate q true) (cons [true] v))=_
    rw [Recipe.plus_value]
    simp only [Recipe.input_value,cons_zero,Recipe.literal_value,List.length_replicate,List.length_cons,List.length_nil,Nat.zero_add,ite_true]

theorem prefix_fold (v : Env n) (w : Word) (q : ℕ) :
    w.foldl (foldWordStep (prefixStep : Expr (n+2)) v) (List.replicate q true)=List.replicate (prefixValue w q) true := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih =>
    rw [List.foldl_cons]
    unfold foldWordStep
    rw [prefixStep_value]
    cases b <;> exact ih _

theorem prefix_poly (W : Expr n) : Poly (foldWordProgram (reverse W) (numeral 0) prefixStep) := by
  obtain ⟨f,hf,h⟩ := W.polynomial
  apply foldWordProgram_poly _ _ _ f hf
  intro N v hv j hj
  change ((((reverse W).value v).take j).foldl (foldWordStep prefixStep v) (List.replicate 0 true)).length≤f N
  rw [prefix_fold,List.length_replicate]
  have hh := prefixValue_bound (((reverse W).value v).take j) 0
  have hw := h N v hv
  rw [Nat.add_zero,List.length_take,reverse_value,List.length_reverse] at hh
  exact hh.trans ((min_le_right _ _).trans ((Nat.le_add_left _ _).trans hw))

def prefixLength (W : Expr n) : Expr n := ⟨foldWordProgram (reverse W) (numeral 0) prefixStep,prefix_poly W⟩

theorem prefix_value (W : Expr n) (v : Env n) : (prefixLength W).value v=List.replicate (headCount (W.value v)) true := by
  change (foldWordProgram (reverse W) (numeral 0) prefixStep).value v=_
  rw [foldWordProgram_value,reverse_value]
  change (W.value v).reverse.foldl (foldWordStep prefixStep v) (List.replicate 0 true)=_
  rw [prefix_fold,prefixValue_reverse]
  simp

@[simp] theorem prefix_number (W : Expr n) (v : Env n) : (prefixLength W).number v=headCount (W.value v) := by
  unfold Expr.number
  rw [prefix_value,List.length_replicate]

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Encoding
open Computation.Stack.PolyRecipe

theorem headCount_le (w : Word) : headCount w≤w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp only [headCount,List.length_cons] <;> omega

theorem header_headCount (w : Word) : header w=
    if headCount w<w.length then some (headCount w,w.drop (headCount w+1)) else none := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false => simp [header,headCount]
    | true =>
      simp only [header,ih,headCount,List.length_cons]
      by_cases h : headCount w<w.length
      · simp [h,List.drop_succ_cons]
      · simp [h]

theorem bits_nonempty {a : ℕ} (h : a≠0) : a.bits≠[] := by
  intro he
  have hv := value_bits a
  rw [he] at hv
  exact h hv.symm

theorem bits_last (a : ℕ) : a.bits=[] ∨ a.bits.getLast?=some true := by
  induction a using Nat.binaryRec' with
  | zero => exact Or.inl rfl
  | bit b a ha ih =>
    rw [Nat.bits_append_bit _ _ ha]
    apply Or.inr
    by_cases h : a=0
    · subst a
      simp [ha rfl]
    · rw [List.getLast?_cons_of_ne_nil (bits_nonempty h)]
      exact ih.resolve_left (bits_nonempty h)

theorem value_positive {w : Word} (h : w.getLast?=some true) : 0<value w := by
  induction w with
  | nil => cases h
  | cons b w ih =>
    by_cases hw : w=[]
    · subst w
      simp only [List.getLast?_singleton,Option.some.injEq] at h
      subst b
      decide
    · rw [List.getLast?_cons_of_ne_nil hw] at h
      have hp := ih h
      change 0<Nat.bit b (value w)
      cases b <;> simp only [Nat.bit_false,Nat.bit_true] <;> omega

theorem canonical_iff (w : Word) : (value w).bits=w ↔ w=[] ∨ w.getLast?=some true := by
  constructor
  · intro h
    simpa only [h] using bits_last (value w)
  · intro h
    induction w with
    | nil => rfl
    | cons b w ih =>
      have hh : (b::w).getLast?=some true := h.resolve_left (by simp)
      by_cases hw : w=[]
      · subst w
        simp only [List.getLast?_singleton,Option.some.injEq] at hh
        subst b
        rfl
      · rw [List.getLast?_cons_of_ne_nil hw] at hh
        have hp := value_positive hh
        change (Nat.bit b (value w)).bits=b::w
        rw [Nat.bits_append_bit _ _ (by omega),ih (Or.inr hh)]

end VariableWL.Encoding

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def take (W C : Expr n) : Expr n := reverse (drop (reverse W) (sub (length W) C))
@[simp] theorem take_value (W C : Expr n) (v : Env n) : (take W C).value v=(W.value v).take (C.number v) := by
  rw [take,reverse_value,drop_value,reverse_value,sub_number,length_number,← List.reverse_take,List.reverse_reverse]

def disj (P Q : Expr n) : Expr n := choose P (literal [true]) Q
@[simp] theorem disj_bit (P Q : Expr n) (v : Env n) : (disj P Q).bit v=(P.bit v || Q.bit v) := by
  rw [disj,choose_bit]
  have ht : (literal [true] : Expr n).bit v=true := rfl
  rw [ht]
  cases P.bit v <;> rfl

def canonical (W : Expr n) : Expr n := disj (eq (length W) (numeral 0)) (reverse W)

theorem canonical_bit (W : Expr n) (v : Env n) : (canonical W).bit v=decide ((Encoding.value (W.value v)).bits=W.value v) := by
  apply Bool.eq_iff_iff.mpr
  rw [canonical,disj_bit,Bool.or_eq_true,eq_bit,decide_eq_true_eq,length_number,numeral_number]
  change ((W.value v).length=0 ∨ decide (((reverse W).value v).head?=some true)=true) ↔ _
  rw [reverse_value,List.head?_reverse,decide_eq_true_eq,decide_eq_true_eq,Encoding.canonical_iff,List.length_eq_zero_iff]

def afterHeader (W : Expr n) : Expr n := drop W (add (prefixLength W) (numeral 1))
def integerBits (W : Expr n) : Expr n := take (afterHeader W) (prefixLength W)
def afterInteger (W : Expr n) : Expr n := drop (afterHeader W) (prefixLength W)
def integerNumber (W C : Expr n) : Expr n := binary (integerBits W) C

def integerValid (W : Expr n) : Expr n := conj (lt (prefixLength W) (length W))
  (conj (le (prefixLength W) (length (afterHeader W))) (canonical (integerBits W)))

@[simp] theorem afterHeader_value (W : Expr n) (v : Env n) :
    (afterHeader W).value v=(W.value v).drop (headCount (W.value v)+1) := by
  rw [afterHeader,drop_value,add_number,prefix_number,numeral_number]
@[simp] theorem integerBits_value (W : Expr n) (v : Env n) :
    (integerBits W).value v=((W.value v).drop (headCount (W.value v)+1)).take (headCount (W.value v)) := by
  rw [integerBits,take_value,afterHeader_value,prefix_number]
@[simp] theorem afterInteger_value (W : Expr n) (v : Env n) :
    (afterInteger W).value v=((W.value v).drop (headCount (W.value v)+1)).drop (headCount (W.value v)) := by
  rw [afterInteger,drop_value,afterHeader_value,prefix_number]

theorem integer_spec (W : Expr n) (v : Env n) : Encoding.integer (W.value v)=
    if (integerValid W).bit v then some (Encoding.value ((integerBits W).value v),(afterInteger W).value v) else none := by
  rw [Encoding.integer,Encoding.header_headCount]
  simp only [integerValid,conj_bit,lt_bit,le_bit,prefix_number,length_number,canonical_bit,
    afterHeader_value,integerBits_value,afterInteger_value]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  split_ifs <;> simp_all

theorem integer_number_exact (W C : Expr n) (v : Env n)
    (h : Encoding.value ((integerBits W).value v)≤C.number v) :
    (integerNumber W C).number v=Encoding.value ((integerBits W).value v) := by
  rw [integerNumber,binary_number,min_eq_left h]

theorem integer_success (W C : Expr n) (v : Env n) (a : ℕ) (t : Word)
    (h : Encoding.value ((integerBits W).value v)≤C.number v) :
    Encoding.integer (W.value v)=some (a,t) ↔
    (integerValid W).bit v=true ∧ (integerNumber W C).number v=a ∧ (afterInteger W).value v=t := by
  rw [integer_spec,integer_number_exact W C v h]
  cases (integerValid W).bit v <;> simp

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Encoding

theorem graph_spec (w u : Word) (a : ℕ) (b : Bool) (hi : integer w=if b then some (a,u) else none)
    (G : Graph) (t : Word) :
    graph w=some (G,t) ↔ (b=true ∧ MatrixValid a (u.take (a*a))) ∧
      G.order=a ∧ matrix G=u.take (a*a) ∧ u.drop (a*a)=t := by
  rw [graph,hi]
  cases b with
  | false => simp
  | true =>
    simp only [ite_true,Option.map_eq_some_iff,true_and]
    constructor
    · rintro ⟨G',hr,he⟩
      cases he
      have hs := readMatrix_sound hr
      have hv := matrix_valid G
      rw [hs.1,hs.2] at hv
      exact ⟨hv,hs.1,hs.2,rfl⟩
    · rintro ⟨hv,hn,hm,ht⟩
      refine ⟨G,?_,by rw [ht]⟩
      rw [← hm,← hn,readMatrix_matrix]

theorem matrix_exists (a : ℕ) (w : Word) (h : MatrixValid a w) :
    ∃G : Graph,G.order=a ∧ matrix G=w :=
  ⟨fromMatrix a w h,rfl,matrix_fromMatrix a w h⟩

end VariableWL.Encoding

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def matrixEntry (A N I J : Expr n) : Expr n := lookup A (add (mul I N) J)
def matrixValid (A N : Expr n) : Expr n :=
  conj (eq (length A) (mul N N))
    (conj (all N (all N.up (bitEq (matrixEntry A.up₂ N.up₂ (input 1) (input 0))
      (matrixEntry A.up₂ N.up₂ (input 0) (input 1)))))
      (all N (neg (matrixEntry A.up N.up (input 0) (input 0)))))

@[simp] theorem matrixEntry_bit (A N I J : Expr n) (v : Env n) :
    (matrixEntry A N I J).bit v=(A.value v).getD (I.number v*N.number v+J.number v) false := by
  rw [matrixEntry,lookup_bit,add_number,mul_number]

theorem matrixValid_bit (A N : Expr n) (v : Env n) :
    (matrixValid A N).bit v=true ↔ Encoding.MatrixValid (N.number v) (A.value v) := by
  simp only [matrixValid,conj_bit,Bool.and_eq_true,eq_bit,decide_eq_true_eq,length_number,mul_number,
    all_bit,List.all_eq_true,List.mem_range,bitEq_bit,matrixEntry_bit,
    up₂_value,up₂_number,up_value,up_number,input_number,cons_zero,NumericProgram.cons_one,
    List.length_replicate,neg_bit,Bool.not_eq_true']
  unfold Encoding.MatrixValid Encoding.entry
  constructor
  · rintro ⟨hlen,hs,hd⟩
    exact ⟨hlen,fun i j=>hs i.val i.isLt j.val j.isLt,fun i=>hd i.val i.isLt⟩
  · rintro ⟨hlen,hs,hd⟩
    exact ⟨hlen,fun i hi j hj=>hs ⟨i,hi⟩ ⟨j,hj⟩,fun i hi=>hd ⟨i,hi⟩⟩

def graphMatrix (W C : Expr n) : Expr n := take (afterInteger W) (mul (integerNumber W C) (integerNumber W C))
def afterGraph (W C : Expr n) : Expr n := drop (afterInteger W) (mul (integerNumber W C) (integerNumber W C))
def graphValid (W C : Expr n) : Expr n := conj (integerValid W) (matrixValid (graphMatrix W C) (integerNumber W C))

@[simp] theorem graphMatrix_value (W C : Expr n) (v : Env n) :
    (graphMatrix W C).value v=((afterInteger W).value v).take ((integerNumber W C).number v*(integerNumber W C).number v) := by
  rw [graphMatrix,take_value,mul_number]
@[simp] theorem afterGraph_value (W C : Expr n) (v : Env n) :
    (afterGraph W C).value v=((afterInteger W).value v).drop ((integerNumber W C).number v*(integerNumber W C).number v) := by
  rw [afterGraph,drop_value,mul_number]

theorem graph_success (W C : Expr n) (v : Env n) (G : Graph) (t : Word)
    (h : Encoding.value ((integerBits W).value v)≤C.number v) :
    Encoding.graph (W.value v)=some (G,t) ↔
    (graphValid W C).bit v=true ∧ G.order=(integerNumber W C).number v ∧
      Encoding.matrix G=(graphMatrix W C).value v ∧ (afterGraph W C).value v=t := by
  have hs := integer_spec W v
  rw [← integer_number_exact W C v h] at hs
  rw [graphValid,conj_bit,Bool.and_eq_true,matrixValid_bit,graphMatrix_value,afterGraph_value]
  exact Encoding.graph_spec _ _ _ _ hs G t

theorem graph_fields_valid (W C : Expr n) (v : Env n) (h : (graphValid W C).bit v=true) :
    Encoding.MatrixValid ((integerNumber W C).number v) ((graphMatrix W C).value v) := by
  rw [graphValid,conj_bit,Bool.and_eq_true,matrixValid_bit] at h
  exact h.2

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem value_le_two_pow (w : Word) : Encoding.value w≤2^w.length := by
  have h := BinaryMachine.value_bound w.reverse 0
  rw [BinaryMachine.value_reverse] at h
  simp only [Nat.zero_mul,Nat.zero_add,List.length_reverse,Nat.one_mul] at h
  omega

theorem integerBits_length (W : Expr n) (v : Env n) : ((integerBits W).value v).length≤(W.value v).length := by
  rw [integerBits_value,List.length_take,List.length_drop]
  omega

def Enough (W C : Expr n) (v : Env n) : Prop := 2^(W.value v).length≤C.number v

theorem enough_integer (W C : Expr n) (v : Env n) (h : Enough W C v) :
    Encoding.value ((integerBits W).value v)≤C.number v :=
  (value_le_two_pow _).trans ((Nat.pow_le_pow_right (by omega) (integerBits_length W v)).trans h)

theorem afterGraph_length (W C : Expr n) (v : Env n) : ((afterGraph W C).value v).length≤(W.value v).length := by
  rw [afterGraph,drop_value,afterInteger_value,List.length_drop,List.length_drop,List.length_drop]
  omega

theorem enough_afterGraph (W C : Expr n) (v : Env n) (h : Enough W C v) : Enough (afterGraph W C) C v :=
  (Nat.pow_le_pow_right (by omega) (afterGraph_length W C v)).trans h

def secondWord (W C : Expr n) : Expr n := afterGraph W C
def dimensionWord (W C : Expr n) : Expr n := afterGraph (secondWord W C) C

def pairValid (W C : Expr n) : Expr n :=
  conj (graphValid W C) (conj (graphValid (secondWord W C) C)
    (conj (integerValid (dimensionWord W C)) (eq (length (afterInteger (dimensionWord W C))) (numeral 0))))

theorem pair_success (W C : Expr n) (v : Env n) (G H : Graph) (k : ℕ) (hc : Enough W C v) :
    Encoding.pair (W.value v)=some (G,H,k) ↔
    (pairValid W C).bit v=true ∧
      G.order=(integerNumber W C).number v ∧ Encoding.matrix G=(graphMatrix W C).value v ∧
      H.order=(integerNumber (secondWord W C) C).number v ∧ Encoding.matrix H=(graphMatrix (secondWord W C) C).value v ∧
      k=(integerNumber (dimensionWord W C) C).number v := by
  have h1 := enough_integer W C v hc
  have hc2 := enough_afterGraph W C v hc
  have h2 := enough_integer (secondWord W C) C v hc2
  have hc3 := enough_afterGraph (secondWord W C) C v hc2
  have h3 := enough_integer (dimensionWord W C) C v hc3
  constructor
  · intro hp
    unfold Encoding.pair at hp
    cases hg : Encoding.graph (W.value v) with
    | none => simp [hg] at hp
    | some q =>
      rcases q with ⟨G',u⟩
      have hG := (graph_success W C v G' u h1).mp hg
      have hu : (secondWord W C).value v=u := hG.2.2.2
      cases hh : Encoding.graph u with
      | none => simp [hg,hh] at hp
      | some q =>
        rcases q with ⟨H',t⟩
        have hH := (graph_success (secondWord W C) C v H' t h2).mp (hu.symm ▸ hh)
        have ht : (dimensionWord W C).value v=t := hH.2.2.2
        cases hk : Encoding.integer t with
        | none => simp [hg,hh,hk] at hp
        | some q =>
          rcases q with ⟨k',z⟩
          have hK := (integer_success (dimensionWord W C) C v k' z h3).mp (ht.symm ▸ hk)
          simp only [hg,hh,hk] at hp
          split_ifs at hp with hz
          cases Option.some.inj hp
          refine ⟨?_,hG.2.1,hG.2.2.1,hH.2.1,hH.2.2.1,hK.2.1.symm⟩
          simp only [pairValid,conj_bit,Bool.and_eq_true,eq_bit,decide_eq_true_eq,length_number,numeral_number]
          exact ⟨hG.1,hH.1,hK.1,by rw [hK.2.2,hz]; rfl⟩
  · rintro ⟨hp,hGn,hGm,hHn,hHm,hk⟩
    simp only [pairValid,conj_bit,Bool.and_eq_true,eq_bit,decide_eq_true_eq,length_number,numeral_number] at hp
    have hg := (graph_success W C v G ((secondWord W C).value v) h1).mpr ⟨hp.1,hGn,hGm,rfl⟩
    have hh := (graph_success (secondWord W C) C v H ((dimensionWord W C).value v) h2).mpr
      ⟨hp.2.1,hHn,hHm,rfl⟩
    have hz : (afterInteger (dimensionWord W C)).value v=[] := List.length_eq_zero_iff.mp hp.2.2.2
    have hki := (integer_success (dimensionWord W C) C v k [] h3).mpr ⟨hp.2.2.1,hk.symm,hz⟩
    simp only [Encoding.pair,hg,hh,hki,ite_true]

theorem pairValid_exists (W C : Expr n) (v : Env n) (hc : Enough W C v) :
    (pairValid W C).bit v=true ↔ ∃G H k,Encoding.pair (W.value v)=some (G,H,k) := by
  constructor
  · intro h
    have h' := h
    simp only [pairValid,conj_bit,Bool.and_eq_true] at h'
    obtain ⟨G,hGn,hGm⟩ := Encoding.matrix_exists _ _ (graph_fields_valid W C v h'.1)
    obtain ⟨H,hHn,hHm⟩ := Encoding.matrix_exists _ _ (graph_fields_valid (secondWord W C) C v h'.2.1)
    refine ⟨G,H,(integerNumber (dimensionWord W C) C).number v,?_⟩
    apply (pair_success W C v G H _ hc).mpr
    exact ⟨h,hGn,hGm,hHn,hHm,rfl⟩
  · rintro ⟨G,H,k,h⟩
    exact ((pair_success W C v G H k hc).mp h).1

end VariableWL.Computation.Stack.PolyRecipe

end OAI
