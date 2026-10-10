import OAI.Combinatorics.VariableWL.Recipe

namespace OAI

namespace VariableWL.Computation.Stack.Recipe
variable {n m : ℕ}

namespace Certified
abbrev reindex (P : Certified n) (φ : Fin n → Fin m) : Certified m := Recipe.reindex P φ
abbrev bind (P : Certified n) (Q : Certified (n+1)) : Certified n := Recipe.bind P Q
end Certified

@[simp] theorem cons_zero (w : Word) (v : Env n) : cons w v 0=w := rfl
@[simp] theorem cons_succ (w : Word) (v : Env n) (i : Fin n) : cons w v i.succ=v i := rfl
@[simp] theorem reindex_value (P : Certified n) (φ : Fin n → Fin m) (v : Env m) :
    (P.reindex φ).value v=P.value (v ∘ φ) := rfl
@[simp] theorem bind_value (P : Certified n) (Q : Certified (n+1)) (v : Env n) :
    (P.bind Q).value v=Q.value (cons (P.value v) v) := rfl
@[simp] theorem input_value (i : Fin n) (v : Env n) : (input i).value v=v i := rfl
@[simp] theorem literal_value (w : Word) (v : Env n) : (literal w).value v=w := rfl
@[simp] theorem cons_comp_succ (w : Word) (v : Env n) : cons w v ∘ Fin.succ=v := rfl

 def unary (P : Certified n) (op : Fin (n+1) → Certified (n+1)) : Certified n := P.bind (op 0)
 def binary (P Q : Certified n) (op : Fin (n+2) → Fin (n+2) → Certified (n+2)) : Certified n :=
  P.bind ((Q.reindex Fin.succ).bind (op 1 0))

 def len (P : Certified n) : Certified n := unary P length
 def plus (P Q : Certified n) : Certified n := binary P Q add
 def minus (P Q : Certified n) : Certified n := binary P Q subtract
 def times (P Q : Certified n) : Certified n := binary P Q multiply
 def cat (P Q : Certified n) : Certified n := binary P Q append
 def rev (P : Certified n) : Certified n := unary P reverse
 def atIndex (P Q : Certified n) : Certified n := binary P Q lookup
 def tailAt (P Q : Certified n) : Certified n := binary P Q drop

@[simp] theorem len_value (P : Certified n) (v : Env n) :
    (len P).value v=List.replicate (P.value v).length true := rfl
@[simp] theorem plus_value (P Q : Certified n) (v : Env n) :
    (plus P Q).value v=List.replicate ((P.value v).length+(Q.value v).length) true := rfl
@[simp] theorem minus_value (P Q : Certified n) (v : Env n) :
    (minus P Q).value v=List.replicate ((P.value v).length-(Q.value v).length) true := rfl
@[simp] theorem times_value (P Q : Certified n) (v : Env n) :
    (times P Q).value v=List.replicate ((P.value v).length*(Q.value v).length) true := rfl
@[simp] theorem cat_value (P Q : Certified n) (v : Env n) :
    (cat P Q).value v=P.value v++Q.value v := rfl
@[simp] theorem rev_value (P : Certified n) (v : Env n) : (rev P).value v=(P.value v).reverse := rfl
@[simp] theorem atIndex_value (P Q : Certified n) (v : Env n) :
    (atIndex P Q).value v=[(P.value v).getD (Q.value v).length false] := rfl
@[simp] theorem tailAt_value (P Q : Certified n) (v : Env n) :
    (tailAt P Q).value v=(P.value v).drop (Q.value v).length := rfl

 def asBool (P : Certified n) : Certified n := P.bind (test (fun h=>h 0==some true))
 def isZero (P : Certified n) : Certified n := P.bind (test (fun h=>h 0==none))
 def choose (B P Q : Certified n) : Certified n :=
  B.bind (headBranch (fun h=>h 0==some true) (P.reindex Fin.succ) (Q.reindex Fin.succ))
 def lessEq (P Q : Certified n) : Certified n := isZero (minus P Q)
 def equal (P Q : Certified n) : Certified n := isZero (plus (minus P Q) (minus Q P))
 def conj (P Q : Certified n) : Certified n :=
  choose P (asBool Q) (literal [false])

@[simp] theorem asBool_value (P : Certified n) (v : Env n) :
    (asBool P).value v=[decide ((P.value v).head?=some true)] := by
  simp only [asBool,bind_value,test_value,cons_zero]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
@[simp] theorem isZero_value (P : Certified n) (v : Env n) :
    (isZero P).value v=[decide ((P.value v).length=0)] := by
  simp only [isZero,bind_value,test_value,cons_zero]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq,List.head?_eq_none_iff,List.length_eq_zero_iff]
@[simp] theorem choose_value (B P Q : Certified n) (v : Env n) :
    (choose B P Q).value v=if (B.value v).head?=some true then P.value v else Q.value v := by
  simp only [choose,bind_value,headBranch,cons_zero,beq_iff_eq,reindex_value,cons_comp_succ]
  split_ifs <;> simp_all
@[simp] theorem lessEq_value (P Q : Certified n) (v : Env n) :
    (lessEq P Q).value v=[decide ((P.value v).length≤(Q.value v).length)] := by
  simp only [lessEq,isZero_value,minus_value,List.length_replicate,Nat.sub_eq_zero_iff_le]
@[simp] theorem equal_value (P Q : Certified n) (v : Env n) :
    (equal P Q).value v=[decide ((P.value v).length=(Q.value v).length)] := by
  simp only [equal,isZero_value,plus_value,minus_value,List.length_replicate]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

@[simp] theorem conj_value (P Q : Certified n) (v : Env n) :
    (conj P Q).value v=[decide ((P.value v).head?=some true) && decide ((Q.value v).head?=some true)] := by
  rw [conj,choose_value]
  split_ifs <;> rename_i h <;> simp [h,asBool_value]

 def liftIndices (φ : Fin n → Fin m) : Fin (n+2) → Fin (m+2) :=
  Fin.cons 0 (Fin.cons 1 (fun i=>(φ i).succ.succ))

 theorem lift_env (φ : Fin n → Fin m) (v : Env m) (a b : Word) :
    cons a (cons b v) ∘ liftIndices φ=cons a (cons b (v ∘ φ)) := by
  funext i
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>?_) i) i <;> rfl

 theorem foldValue_reindex (Q : Certified (n+2)) (φ : Fin n → Fin m) (v : Env m) (w : Word) (j : ℕ) :
    foldValue (Q.reindex (liftIndices φ)) v w j=foldValue Q (v ∘ φ) w j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [foldValue,reindex_value,ih,lift_env]

 def iterate (B Z : Certified n) (Q : Certified (n+2)) : Certified n :=
  B.bind ((Z.reindex Fin.succ).bind (fold 1 0 (Q.reindex (liftIndices (fun i=>i.succ.succ)))))

 theorem iterate_value (B Z : Certified n) (Q : Certified (n+2)) (v : Env n) :
    (iterate B Z Q).value v=foldValue Q v (Z.value v) (B.value v).length := by
  simp only [iterate,bind_value,reindex_value,cons_comp_succ,fold,cons_zero]
  change foldValue _ (cons (Z.value v) (cons (B.value v) v)) (Z.value v) (B.value v).length=_
  rw [foldValue_reindex]
  rfl

 def collect (B : Certified n) (Q : Certified (n+1)) : Certified n :=
  iterate B (literal []) (cat (input 0) (asBool (Q.reindex Fin.succ)))

 theorem collect_value (B : Certified n) (Q : Certified (n+1)) (v : Env n) :
    (collect B Q).value v=(List.range (B.value v).length).map
      (fun i=>decide ((Q.value (cons (List.replicate i true) v)).head?=some true)) := by
  rw [collect,iterate_value]
  generalize (B.value v).length=j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [foldValue,cat_value,input_value,cons_zero,ih,asBool_value,reindex_value,cons_comp_succ]
    rw [List.range_succ,List.map_append]
    rfl

@[simp] theorem decide_bool (b : Bool) : decide (b=true)=b := by cases b <;> rfl

 def all (B : Certified n) (Q : Certified (n+1)) : Certified n :=
  iterate B (literal [true]) (conj (input 0) (Q.reindex Fin.succ))

 theorem all_value (B : Certified n) (Q : Certified (n+1)) (v : Env n) :
    (all B Q).value v=[(List.range (B.value v).length).all
      (fun i=>decide ((Q.value (cons (List.replicate i true) v)).head?=some true))] := by
  rw [all,iterate_value]
  generalize (B.value v).length=j
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [foldValue,conj_value,input_value,cons_zero,ih,List.head?_cons,
      reindex_value,cons_comp_succ,List.range_succ,List.all_append,
      List.all_cons,List.all_nil,Bool.and_true,Option.some.injEq,decide_bool]
    rfl

 def countTrue (B : Certified n) (Q : Certified (n+1)) : Certified n :=
  iterate B (literal []) (choose (Q.reindex Fin.succ) (cat (literal [true]) (input 0)) (input 0))

 theorem countTrue_value (B : Certified n) (Q : Certified (n+1)) (v : Env n) :
    (countTrue B Q).value v=List.replicate ((List.range (B.value v).length).countP
      (fun i=>decide ((Q.value (cons (List.replicate i true) v)).head?=some true))) true := by
  rw [countTrue,iterate_value]
  generalize (B.value v).length=j
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [foldValue,choose_value,reindex_value,cons_comp_succ,cat_value,literal_value,
      input_value,cons_zero,List.range_succ,List.countP_append,List.countP_cons,List.countP_nil,
      Nat.zero_add]
    split_ifs <;> rename_i h <;> simp_all [List.replicate_succ]

 def power (B E : Certified n) : Certified n :=
  iterate E (literal [true]) (times (input 0) (B.reindex (fun i=>i.succ.succ)))

 theorem power_value (B E : Certified n) (v : Env n) :
    (power B E).value v=List.replicate ((B.value v).length^(E.value v).length) true := by
  rw [power,iterate_value]
  generalize (E.value v).length=j
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [foldValue,times_value,input_value,cons_zero,ih,List.length_replicate,reindex_value,pow_succ]
    rfl

end VariableWL.Computation.Stack.Recipe

namespace VariableWL.Computation.Stack.Recipe
variable {n : ℕ}

 theorem count_range_lt (a b : ℕ) :
    (List.range a).countP (fun i=>decide (i<b))=min a b := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ,List.countP_append,ih]
    simp only [List.countP_cons,List.countP_nil,Nat.zero_add]
    split_ifs <;> rename_i h <;> simp only [decide_eq_true_eq] at h <;> omega

 theorem count_range_multiples (a b : ℕ) (hb : 0<b) :
    (List.range a).countP (fun i=>decide ((i+1)*b≤a))=a/b := by
  have he : (List.range a).countP (fun i=>decide ((i+1)*b≤a))=
      (List.range a).countP (fun i=>decide (i<a/b)) := by
    apply List.countP_congr
    intro i _
    simp only [decide_eq_true_eq,←Nat.le_div_iff_mul_le hb]
    omega
  rw [he,count_range_lt,min_eq_right (Nat.div_le_self a b)]

 def divide (i j : Fin n) : Certified n :=
  choose (isZero (input j)) (literal [])
    (countTrue (input i) (lessEq (times (plus (input 0) (literal [true])) (input j.succ)) (input i.succ)))

 theorem divide_value (i j : Fin n) (v : Env n) :
    (divide i j).value v=List.replicate ((v i).length/(v j).length) true := by
  rw [divide,choose_value]
  by_cases h : (v j).length=0
  · have hz : ((isZero (input j)).value v).head?=some true := by
      rw [isZero_value,input_value]
      simp only [h,decide_true,List.head?_cons]
    rw [ite_eq_left hz,literal_value,h,Nat.div_zero,List.replicate_zero]
  · have hz : ((isZero (input j)).value v).head?≠some true := by
      rw [isZero_value,input_value]
      simp only [h,decide_false,List.head?_cons,ne_eq,Option.some.injEq,Bool.false_eq_true,not_false_eq_true]
    rw [ite_eq_right hz,countTrue_value]
    simp only [lessEq_value,times_value,plus_value,input_value,cons_zero,cons_succ,
      literal_value,List.length_replicate,List.length_cons,List.length_nil,Nat.zero_add,
      List.head?_cons,Option.some.injEq,decide_bool]
    rw [count_range_multiples _ _ (by omega)]

 def quotient (A B : Certified n) : Certified n := binary A B divide
 def remainder (A B : Certified n) : Certified n := minus A (times (quotient A B) B)

 theorem quotient_value (A B : Certified n) (v : Env n) :
    (quotient A B).value v=List.replicate ((A.value v).length/(B.value v).length) true := by
  simp only [quotient,binary,bind_value,reindex_value,cons_comp_succ,divide_value]
  rfl

 theorem remainder_value (A B : Certified n) (v : Env n) :
    (remainder A B).value v=List.replicate ((A.value v).length%(B.value v).length) true := by
  simp only [remainder,minus_value,times_value,quotient_value,List.length_replicate,Nat.mod_eq_sub_div_mul]

 def minimum (A B : Certified n) : Certified n := choose (lessEq A B) (len A) (len B)
 theorem minimum_value (A B : Certified n) (v : Env n) :
    (minimum A B).value v=List.replicate (min (A.value v).length (B.value v).length) true := by
  simp only [minimum,choose_value,lessEq_value,List.head?_cons,Option.some.injEq,decide_eq_true_eq,len_value,Nat.min_def]
  split_ifs <;> rfl

 theorem min_mul_cap (x c b : ℕ) : min (min x c*b) c=min (x*b) c := by
  by_cases hb : b=0
  · simp [hb]
  · have h : c≤c*b := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left c (show 1≤b by omega)
    rw [←Nat.mul_min_mul_right,min_assoc,min_eq_right h]

 def boundedPower (B E C : Certified n) : Certified n :=
  iterate E (minimum (literal [true]) C)
    (minimum (times (input 0) (B.reindex (fun i=>i.succ.succ))) (C.reindex (fun i=>i.succ.succ)))

 theorem boundedPower_value (B E C : Certified n) (v : Env n) :
    (boundedPower B E C).value v=List.replicate (min ((B.value v).length^(E.value v).length) (C.value v).length) true := by
  rw [boundedPower,iterate_value]
  generalize (E.value v).length=j
  induction j with
  | zero => rw [foldValue,minimum_value,literal_value]; rfl
  | succ j ih =>
    rw [foldValue,minimum_value,times_value,input_value,cons_zero,ih,List.length_replicate]
    simp only [List.length_replicate,reindex_value]
    change List.replicate (min (min ((B.value v).length^j) (C.value v).length*(B.value v).length)
      (C.value v).length) true=_
    rw [min_mul_cap,pow_succ]

end VariableWL.Computation.Stack.Recipe

namespace VariableWL.Computation.Stack.Recipe
variable {n m : ℕ}

def Growth (f : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀N, f N≤c*(N+1)^d

namespace Growth
 theorem constant (a : ℕ) : Growth (fun _=>a) := ⟨a,0,by intro N; simp⟩
 theorem ident : Growth id := ⟨1,1,by intro N; simp⟩
 theorem mono {f g : ℕ → ℕ} (hg : Growth g) (h : ∀N,f N≤g N) : Growth f := by
  obtain ⟨c,d,hg⟩ := hg
  exact ⟨c,d,fun N=>(h N).trans (hg N)⟩
 theorem add {f g : ℕ → ℕ} (hf : Growth f) (hg : Growth g) : Growth (fun N=>f N+g N) := by
  obtain ⟨a,b,ha⟩ := hf
  obtain ⟨c,d,hc⟩ := hg
  refine ⟨a+c,b+d,fun N=>?_⟩
  have h1 := (ha N).trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by omega : 0<N+1) (by omega : b≤b+d)))
  have h2 := (hc N).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by omega : 0<N+1) (by omega : d≤b+d)))
  nlinarith
 theorem mul {f g : ℕ → ℕ} (hf : Growth f) (hg : Growth g) : Growth (fun N=>f N*g N) := by
  obtain ⟨a,b,ha⟩ := hf
  obtain ⟨c,d,hc⟩ := hg
  refine ⟨a*c,b+d,fun N=>?_⟩
  exact (Nat.mul_le_mul (ha N) (hc N)).trans_eq (by rw [pow_add]; ring)
 theorem comp {f g : ℕ → ℕ} (hf : Growth f) (hg : Growth g) : Growth (f ∘ g) := by
  obtain ⟨a,b,ha⟩ := hf
  obtain ⟨c,d,hc⟩ := hg
  refine ⟨a*(c+1)^b,d*b,fun N=>?_⟩
  have hpos : 1≤(N+1)^d := Nat.succ_le_of_lt (pow_pos (by omega) _)
  have hh : g N+1≤(c+1)*(N+1)^d := by have := hc N; nlinarith
  refine (ha (g N)).trans ((Nat.mul_le_mul_left a (Nat.pow_le_pow_left hh b)).trans_eq ?_)
  rw [mul_pow,←pow_mul]
  ring
 theorem pow {f : ℕ → ℕ} (hf : Growth f) (d : ℕ) : Growth (fun N=>(f N)^d) := by
  induction d with
  | zero => simpa only [pow_zero] using constant 1
  | succ d ih => simpa only [pow_succ] using mul ih hf
end Growth

def EnvBound (C : ℕ) (v : Env n) : Prop := ∀i,(v i).length≤C

def Poly (P : Certified n) : Prop := ∃f : ℕ → ℕ, Growth f ∧
  ∀C v, EnvBound C v → P.time v+(P.value v).length≤f C

 theorem envBound_cons {C : ℕ} {v : Env n} {w : Word} (hv : EnvBound C v) (hw : w.length≤C) :
    EnvBound C (cons w v) := by
  intro i
  exact Fin.cases hw (fun j=>hv j) i

 theorem poly_of_bound (P : Certified n) (c d : ℕ)
    (h : ∀C v,EnvBound C v → P.time v+(P.value v).length≤c*(C+1)^d) : Poly P :=
  ⟨fun C=>c*(C+1)^d,⟨c,d,fun _=>le_rfl⟩,h⟩

 theorem poly_reindex {P : Certified n} (h : Poly P) (φ : Fin n → Fin m) : Poly (P.reindex φ) := by
  obtain ⟨f,hf,hP⟩ := h
  refine ⟨f,hf,fun C v hv=>hP C (v ∘ φ) (fun i=>hv (φ i))⟩

 theorem poly_input (i : Fin n) : Poly (input i) := by
  apply poly_of_bound _ 13 1
  intro C v hv
  have := hv i
  change 9*(v i).length+3+(v i).length≤13*(C+1)^1
  simp only [pow_one]
  omega

 theorem poly_literal (w : Word) : Poly (literal (n := n) w) := by
  exact ⟨fun _=>1+3*w.length,Growth.constant _,by intro C v hv; change 1+2*w.length+w.length≤1+3*w.length; omega⟩

 theorem poly_bind {P : Certified n} {Q : Certified (n+1)} (hP : Poly P) (hQ : Poly Q) : Poly (P.bind Q) := by
  obtain ⟨f,hf,hP⟩ := hP
  obtain ⟨g,hg,hQ⟩ := hQ
  refine ⟨fun C=>4*f C+g (f C+C)+2,?_,?_⟩
  · exact ((Growth.constant 4 |>.mul hf).add (hg.comp (hf.add Growth.ident))).add (Growth.constant 2)
  · intro C v hv
    have h1 := hP C v hv
    have hev : EnvBound (f C+C) (cons (P.value v) v) :=
      envBound_cons (fun i=>(hv i).trans (by omega)) (by omega)
    have h2 := hQ (f C+C) (cons (P.value v) v) hev
    change P.time v+Q.time (cons (P.value v) v)+3*(P.value v).length+2+
      (Q.value (cons (P.value v) v)).length≤4*f C+g (f C+C)+2
    omega

 theorem poly_headBranch (p : (Fin n → Option Bool) → Bool) {P Q : Certified n}
    (hP : Poly P) (hQ : Poly Q) : Poly (headBranch p P Q) := by
  obtain ⟨f,hf,hP⟩ := hP
  obtain ⟨g,hg,hQ⟩ := hQ
  refine ⟨fun C=>f C+g C+1,(hf.add hg).add (Growth.constant 1),?_⟩
  intro C v hv
  have h1 := hP C v hv
  have h2 := hQ C v hv
  change (if p (fun i=>(v i).head?) then P.time v else Q.time v)+1+
    (if p (fun i=>(v i).head?) then P.value v else Q.value v).length≤f C+g C+1
  split <;> omega

 theorem poly_test (p : (Fin n → Option Bool) → Bool) : Poly (test p) :=
  poly_headBranch p (poly_literal _) (poly_literal _)

 theorem poly_length (i : Fin n) : Poly (length i) := by
  apply poly_of_bound _ 21 1
  intro C v hv
  have := hv i
  change 20*((v i).length+1)+(List.replicate (v i).length true).length≤_
  simp only [List.length_replicate,pow_one]
  omega

 theorem poly_add (i j : Fin n) : Poly (add i j) := by
  apply poly_of_bound _ 42 1
  intro C v hv
  have := hv i
  have := hv j
  change 20*((v i).length+(v j).length+1)+(List.replicate ((v i).length+(v j).length) true).length≤_
  simp only [List.length_replicate,pow_one]
  omega

 theorem poly_subtract (i j : Fin n) : Poly (subtract i j) := by
  apply poly_of_bound _ 42 1
  intro C v hv
  have := hv i
  have := hv j
  change 20*((v i).length+(v j).length+1)+(List.replicate ((v i).length-(v j).length) true).length≤_
  simp only [List.length_replicate,pow_one]
  omega

 theorem poly_multiply (i j : Fin n) : Poly (multiply i j) := by
  apply poly_of_bound _ 31 2
  intro C v hv
  have h1 := hv i
  have h2 := hv j
  have hh := Nat.mul_le_mul h1 h2
  change 20*((v i).length+1)*((v j).length+1)+10+
    (List.replicate ((v i).length*(v j).length) true).length≤_
  simp only [List.length_replicate,pow_two]
  nlinarith

 theorem poly_reverse (i : Fin n) : Poly (reverse i) := by
  apply poly_of_bound _ 21 1
  intro C v hv
  have := hv i
  change 20*((v i).length+1)+(v i).reverse.length≤_
  simp only [List.length_reverse,pow_one]
  omega

 theorem poly_append (i j : Fin n) : Poly (append i j) := by
  apply poly_of_bound _ 42 1
  intro C v hv
  have := hv i
  have := hv j
  change 20*((v i).length+(v j).length+1)+((v i)++(v j)).length≤_
  simp only [List.length_append,pow_one]
  omega

 theorem poly_drop (i j : Fin n) : Poly (drop i j) := by
  apply poly_of_bound _ 36 1
  intro C v hv
  have := hv i
  have := hv j
  change 24*((v i).length+1)+11*(v j).length+((v i).drop (v j).length).length≤_
  simp only [List.length_drop,pow_one]
  omega

 theorem poly_lookup (i j : Fin n) : Poly (lookup i j) := by
  apply poly_of_bound _ 24 1
  intro C v hv
  have := hv i
  have := hv j
  change 12*(v i).length+11*(v j).length+12+[_].length≤_
  simp only [List.length_cons,List.length_nil,pow_one]
  omega

 theorem poly_unary {P : Certified n} (o : Fin (n+1) → Certified (n+1))
    (hP : Poly P) (ho : ∀i,Poly (o i)) : Poly (unary P o) := poly_bind hP (ho _)

 theorem poly_binary {P Q : Certified n} (o : Fin (n+2) → Fin (n+2) → Certified (n+2))
    (hP : Poly P) (hQ : Poly Q) (ho : ∀i j,Poly (o i j)) : Poly (binary P Q o) :=
  poly_bind hP (poly_bind (poly_reindex hQ Fin.succ) (ho _ _))

 theorem poly_len {P : Certified n} (hP : Poly P) : Poly (len P) := poly_unary length hP poly_length
 theorem poly_plus {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (plus P Q) := poly_binary add hP hQ poly_add
 theorem poly_minus {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (minus P Q) := poly_binary subtract hP hQ poly_subtract
 theorem poly_times {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (times P Q) := poly_binary multiply hP hQ poly_multiply
 theorem poly_cat {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (cat P Q) := poly_binary append hP hQ poly_append
 theorem poly_rev {P : Certified n} (hP : Poly P) : Poly (rev P) := poly_unary reverse hP poly_reverse
 theorem poly_atIndex {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (atIndex P Q) := poly_binary lookup hP hQ poly_lookup
 theorem poly_tailAt {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (tailAt P Q) := poly_binary drop hP hQ poly_drop
 theorem poly_asBool {P : Certified n} (hP : Poly P) : Poly (asBool P) := poly_bind hP (poly_test _)
 theorem poly_isZero {P : Certified n} (hP : Poly P) : Poly (isZero P) := poly_bind hP (poly_test _)
 theorem poly_choose {B P Q : Certified n} (hB : Poly B) (hP : Poly P) (hQ : Poly Q) : Poly (choose B P Q) :=
  poly_bind hB (poly_headBranch _ (poly_reindex hP _) (poly_reindex hQ _))
 theorem poly_lessEq {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (lessEq P Q) := poly_isZero (poly_minus hP hQ)
 theorem poly_equal {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (equal P Q) :=
  poly_isZero (poly_plus (poly_minus hP hQ) (poly_minus hQ hP))
 theorem poly_conj {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (conj P Q) :=
  poly_choose hP (poly_asBool hQ) (poly_literal _)
 theorem poly_minimum {P Q : Certified n} (hP : Poly P) (hQ : Poly Q) : Poly (minimum P Q) :=
  poly_choose (poly_lessEq hP hQ) (poly_len hP) (poly_len hQ)

end VariableWL.Computation.Stack.Recipe

end OAI
