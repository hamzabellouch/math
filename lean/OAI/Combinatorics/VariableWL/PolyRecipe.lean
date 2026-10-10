import OAI.Combinatorics.VariableWL.CertifiedRecipe

namespace OAI

namespace VariableWL.Computation.Stack.Recipe
variable {n m : ℕ}

@[simp] theorem reindex_time (P : Certified n) (φ : Fin n → Fin m) (v : Env m) :
    (P.reindex φ).time v=P.time (v ∘ φ) := rfl
@[simp] theorem bind_time (P : Certified n) (Q : Certified (n+1)) (v : Env n) :
    (P.bind Q).time v=P.time v+Q.time (cons (P.value v) v)+3*(P.value v).length+2 := rfl
 theorem fold_time (b z : Fin n) (Q : Certified (n+2)) (v : Env n) :
    (fold b z Q).time v=9*(v z).length+9*(v b).length+
      BoundedLoop.total (v b).length (foldTime Q v (v z))+
      12*(foldValue Q v (v z) (v b).length).length+20 := rfl

 theorem foldTime_reindex (Q : Certified (n+2)) (φ : Fin n → Fin m) (v : Env m) (w : Word) (j : ℕ) :
    foldTime (Q.reindex (liftIndices φ)) v w j=foldTime Q (v ∘ φ) w j := by
  simp only [foldTime,reindex_time,foldValue_reindex,lift_env]

 theorem iterate_time (B Z : Certified n) (Q : Certified (n+2)) (v : Env n) :
    (iterate B Z Q).time v=B.time v+Z.time v+12*(B.value v).length+12*(Z.value v).length+
      BoundedLoop.total (B.value v).length (foldTime Q v (Z.value v))+
      12*(foldValue Q v (Z.value v) (B.value v).length).length+24 := by
  simp only [iterate,bind_time,reindex_time,cons_comp_succ,fold_time]
  change B.time v+(Z.time v+(9*(Z.value v).length+9*(B.value v).length+
    BoundedLoop.total (B.value v).length (foldTime (Q.reindex (liftIndices (fun i=>i.succ.succ)))
      (cons (Z.value v) (cons (B.value v) v)) (Z.value v))+
    12*(foldValue (Q.reindex (liftIndices (fun i=>i.succ.succ)))
      (cons (Z.value v) (cons (B.value v) v)) (Z.value v) (B.value v).length).length+20)+
    3*(Z.value v).length+2)+3*(B.value v).length+2=_
  have he : foldTime (Q.reindex (liftIndices (fun i=>i.succ.succ)))
      (cons (Z.value v) (cons (B.value v) v)) (Z.value v)=foldTime Q v (Z.value v) := by
    funext j
    rw [foldTime_reindex]
    rfl
  rw [he,foldValue_reindex]
  change B.time v+(Z.time v+(9*(Z.value v).length+9*(B.value v).length+
    BoundedLoop.total (B.value v).length (foldTime Q v (Z.value v))+
    12*(foldValue Q v (Z.value v) (B.value v).length).length+20)+
    3*(Z.value v).length+2)+3*(B.value v).length+2=_
  omega

 theorem poly_iterate {B Z : Certified n} {Q : Certified (n+2)}
    (hB : Poly B) (hZ : Poly Z) (hQ : Poly Q)
    (f : ℕ → ℕ) (hf : Growth f)
    (hacc : ∀C v,EnvBound C v → ∀j≤(B.value v).length,(foldValue Q v (Z.value v) j).length≤f C) :
    Poly (iterate B Z Q) := by
  obtain ⟨b,hb,hB⟩ := hB
  obtain ⟨z,hz,hZ⟩ := hZ
  obtain ⟨q,hq,hQ⟩ := hQ
  let D : ℕ → ℕ := fun C=>b C+f C+C
  have hD : Growth D := (hb.add hf).add Growth.ident
  refine ⟨fun C=>13*(b C+z C+f C)+(q (D C)+3*f C+6)*b C+24,?_,?_⟩
  · exact (((Growth.constant 13).mul ((hb.add hz).add hf)).add
      ((((hq.comp hD).add ((Growth.constant 3).mul hf)).add (Growth.constant 6)).mul hb)).add (Growth.constant 24)
  · intro C v hv
    have h1 := hB C v hv
    have h2 := hZ C v hv
    have h3 := hacc C v hv (B.value v).length le_rfl
    have hcost (j : ℕ) (hj : j<(B.value v).length) : foldTime Q v (Z.value v) j≤q (D C)+3*f C+2 := by
      have h4 := hacc C v hv j (by omega)
      have hev : EnvBound (D C) (cons (foldValue Q v (Z.value v) j) (cons (List.replicate j true) v)) := by
        apply envBound_cons
        · apply envBound_cons
          · intro i; have := hv i; dsimp only [D]; omega
          · simp only [List.length_replicate]; dsimp only [D]; omega
        · dsimp only [D]; omega
      have h5 := hQ (D C) _ hev
      unfold foldTime
      omega
    have htot := BoundedLoop.total_bound (B.value v).length (q (D C)+3*f C+2) _ hcost
    have htot' : BoundedLoop.total (B.value v).length (foldTime Q v (Z.value v))≤
        (q (D C)+3*f C+6)*b C := by
      apply htot.trans
      have hm := Nat.mul_le_mul_left (q (D C)+3*f C+6) (show (B.value v).length≤b C by omega)
      simpa only [Nat.add_assoc] using hm
    rw [iterate_time,iterate_value]
    change B.time v+Z.time v+12*(B.value v).length+12*(Z.value v).length+
      BoundedLoop.total (B.value v).length (foldTime Q v (Z.value v))+
      12*(foldValue Q v (Z.value v) (B.value v).length).length+24+
      (foldValue Q v (Z.value v) (B.value v).length).length≤
      13*(b C+z C+f C)+(q (D C)+3*f C+6)*b C+24
    omega

 theorem collect_prefix (Q : Certified (n+1)) (v : Env n) (j : ℕ) :
    (foldValue (cat (input 0) (asBool (Q.reindex Fin.succ))) v [] j).length=j := by
  have h := collect_value (literal (List.replicate j true)) Q v
  rw [collect,iterate_value] at h
  simp only [literal_value,List.length_replicate] at h
  rw [h,List.length_map,List.length_range]

 theorem all_prefix (Q : Certified (n+1)) (v : Env n) (j : ℕ) :
    (foldValue (conj (input 0) (Q.reindex Fin.succ)) v [true] j).length=1 := by
  have h := all_value (literal (List.replicate j true)) Q v
  rw [all,iterate_value] at h
  simp only [literal_value,List.length_replicate] at h
  rw [h]
  rfl

 theorem countTrue_prefix (Q : Certified (n+1)) (v : Env n) (j : ℕ) :
    (foldValue (choose (Q.reindex Fin.succ) (cat (literal [true]) (input 0)) (input 0)) v [] j).length≤j := by
  have h := countTrue_value (literal (List.replicate j true)) Q v
  rw [countTrue,iterate_value] at h
  simp only [literal_value,List.length_replicate] at h
  rw [h,List.length_replicate]
  exact (List.countP_le_length).trans_eq (List.length_range (n := j))

 theorem poly_collect {B : Certified n} {Q : Certified (n+1)} (hB : Poly B) (hQ : Poly Q) : Poly (collect B Q) := by
  obtain ⟨b,hb,h⟩ := hB
  apply poly_iterate ⟨b,hb,h⟩ (poly_literal _) (poly_cat (poly_input _) (poly_asBool (poly_reindex hQ _))) b hb
  intro C v hv j hj
  rw [literal_value,collect_prefix]
  have hh := h C v hv
  omega

 theorem poly_all {B : Certified n} {Q : Certified (n+1)} (hB : Poly B) (hQ : Poly Q) : Poly (all B Q) := by
  apply poly_iterate hB (poly_literal _) (poly_conj (poly_input _) (poly_reindex hQ _)) (fun _=>1) (Growth.constant 1)
  intro C v hv j hj
  rw [literal_value,all_prefix]

 theorem poly_countTrue {B : Certified n} {Q : Certified (n+1)} (hB : Poly B) (hQ : Poly Q) : Poly (countTrue B Q) := by
  obtain ⟨b,hb,h⟩ := hB
  apply poly_iterate ⟨b,hb,h⟩ (poly_literal _)
    (poly_choose (poly_reindex hQ _) (poly_cat (poly_literal _) (poly_input _)) (poly_input _)) b hb
  intro C v hv j hj
  rw [literal_value]
  have hh := h C v hv
  exact (countTrue_prefix Q v j).trans (by omega)

 theorem poly_divide (i j : Fin n) : Poly (divide i j) :=
  poly_choose (poly_isZero (poly_input _)) (poly_literal _)
    (poly_countTrue (poly_input _) (poly_lessEq (poly_times (poly_plus (poly_input _) (poly_literal _)) (poly_input _)) (poly_input _)))

 theorem poly_quotient {A B : Certified n} (hA : Poly A) (hB : Poly B) : Poly (quotient A B) :=
  poly_binary divide hA hB poly_divide
 theorem poly_remainder {A B : Certified n} (hA : Poly A) (hB : Poly B) : Poly (remainder A B) :=
  poly_minus hA (poly_times (poly_quotient hA hB) hB)

 theorem boundedPower_prefix (B C : Certified n) (v : Env n) (j : ℕ) :
    (foldValue (minimum (times (input 0) (B.reindex (fun i=>i.succ.succ))) (C.reindex (fun i=>i.succ.succ)))
      v ((minimum (literal [true]) C).value v) j).length≤(C.value v).length := by
  have h := boundedPower_value B (literal (List.replicate j true)) C v
  rw [boundedPower,iterate_value] at h
  simp only [literal_value,List.length_replicate] at h
  rw [h,List.length_replicate]
  exact min_le_right _ _

 theorem poly_boundedPower {B E C : Certified n} (hB : Poly B) (hE : Poly E) (hC : Poly C) :
    Poly (boundedPower B E C) := by
  obtain ⟨c,hc,h⟩ := hC
  apply poly_iterate hE (poly_minimum (poly_literal _) ⟨c,hc,h⟩)
    (poly_minimum (poly_times (poly_input _) (poly_reindex hB _)) (poly_reindex ⟨c,hc,h⟩ _)) c hc
  intro N v hv j hj
  have hh := h N v hv
  exact (boundedPower_prefix B C v j).trans (by omega)

end VariableWL.Computation.Stack.Recipe

namespace VariableWL.Computation.Stack
namespace PolyRecipe
open Recipe

structure Expr (n : ℕ) where
  program : Certified n
  polynomial : Poly program

variable {n m : ℕ}
def Expr.value (P : Expr n) := P.program.value
def Expr.number (P : Expr n) (v : Env n) := (P.value v).length
def Expr.bit (P : Expr n) (v : Env n) := decide ((P.value v).head?=some true)
def Expr.reindex (P : Expr n) (φ : Fin n → Fin m) : Expr m :=
  ⟨P.program.reindex φ,poly_reindex P.polynomial φ⟩
def Expr.up (P : Expr n) : Expr (n+1) := P.reindex Fin.succ
def Expr.up₂ (P : Expr n) : Expr (n+2) := P.reindex (fun i=>i.succ.succ)
def input (i : Fin n) : Expr n := ⟨Recipe.input i,poly_input i⟩
def literal (w : Word) : Expr n := ⟨Recipe.literal w,poly_literal w⟩
def numeral (a : ℕ) : Expr n := literal (List.replicate a true)
def add (P Q : Expr n) : Expr n := ⟨plus P.program Q.program,poly_plus P.polynomial Q.polynomial⟩
def sub (P Q : Expr n) : Expr n := ⟨minus P.program Q.program,poly_minus P.polynomial Q.polynomial⟩
def mul (P Q : Expr n) : Expr n := ⟨times P.program Q.program,poly_times P.polynomial Q.polynomial⟩
def div (P Q : Expr n) : Expr n := ⟨quotient P.program Q.program,poly_quotient P.polynomial Q.polynomial⟩
def mod (P Q : Expr n) : Expr n := ⟨remainder P.program Q.program,poly_remainder P.polynomial Q.polynomial⟩
def capPow (P Q C : Expr n) : Expr n :=
  ⟨boundedPower P.program Q.program C.program,poly_boundedPower P.polynomial Q.polynomial C.polynomial⟩
def eq (P Q : Expr n) : Expr n := ⟨equal P.program Q.program,poly_equal P.polynomial Q.polynomial⟩
def le (P Q : Expr n) : Expr n := ⟨lessEq P.program Q.program,poly_lessEq P.polynomial Q.polynomial⟩
def choose (B P Q : Expr n) : Expr n :=
  ⟨Recipe.choose B.program P.program Q.program,poly_choose B.polynomial P.polynomial Q.polynomial⟩
def neg (P : Expr n) : Expr n := choose P (literal [false]) (literal [true])
def lt (P Q : Expr n) : Expr n := neg (le Q P)
def conj (P Q : Expr n) : Expr n := ⟨Recipe.conj P.program Q.program,poly_conj P.polynomial Q.polynomial⟩
def bitEq (P Q : Expr n) : Expr n := choose P Q (neg Q)
def lookup (P Q : Expr n) : Expr n := ⟨atIndex P.program Q.program,poly_atIndex P.polynomial Q.polynomial⟩
def all (B : Expr n) (Q : Expr (n+1)) : Expr n := ⟨Recipe.all B.program Q.program,poly_all B.polynomial Q.polynomial⟩
def collect (B : Expr n) (Q : Expr (n+1)) : Expr n :=
  ⟨Recipe.collect B.program Q.program,poly_collect B.polynomial Q.polynomial⟩
def count (B : Expr n) (Q : Expr (n+1)) : Expr n :=
  ⟨countTrue B.program Q.program,poly_countTrue B.polynomial Q.polynomial⟩

@[simp] theorem reindex_value (P : Expr n) (φ : Fin n → Fin m) (v : Env m) :
    (P.reindex φ).value v=P.value (v ∘ φ) := rfl
@[simp] theorem up_value (P : Expr n) (v : Env n) (w : Word) : P.up.value (cons w v)=P.value v := rfl
@[simp] theorem up₂_value (P : Expr n) (v : Env n) (w z : Word) : P.up₂.value (cons z (cons w v))=P.value v := rfl
@[simp] theorem input_value (i : Fin n) (v : Env n) : (input i).value v=v i := rfl
@[simp] theorem literal_value (w : Word) (v : Env n) : (literal w).value v=w := rfl
@[simp] theorem numeral_number (a : ℕ) (v : Env n) : (numeral a).number v=a := List.length_replicate ..
@[simp] theorem reindex_number (P : Expr n) (φ : Fin n → Fin m) (v : Env m) :
    (P.reindex φ).number v=P.number (v ∘ φ) := rfl
@[simp] theorem up_number (P : Expr n) (v : Env n) (w : Word) : P.up.number (cons w v)=P.number v := rfl
@[simp] theorem up₂_number (P : Expr n) (v : Env n) (w z : Word) : P.up₂.number (cons z (cons w v))=P.number v := rfl
@[simp] theorem input_number (i : Fin n) (v : Env n) : (input i).number v=(v i).length := rfl
@[simp] theorem add_number (P Q : Expr n) (v : Env n) : (add P Q).number v=P.number v+Q.number v := by
  simp only [Expr.number,Expr.value,add,plus_value,List.length_replicate]
@[simp] theorem sub_number (P Q : Expr n) (v : Env n) : (sub P Q).number v=P.number v-Q.number v := by
  simp only [Expr.number,Expr.value,sub,minus_value,List.length_replicate]
@[simp] theorem mul_number (P Q : Expr n) (v : Env n) : (mul P Q).number v=P.number v*Q.number v := by
  simp only [Expr.number,Expr.value,mul,times_value,List.length_replicate]
@[simp] theorem div_number (P Q : Expr n) (v : Env n) : (div P Q).number v=P.number v/Q.number v := by
  simp only [Expr.number,Expr.value,div,quotient_value,List.length_replicate]
@[simp] theorem mod_number (P Q : Expr n) (v : Env n) : (mod P Q).number v=P.number v%Q.number v := by
  simp only [Expr.number,Expr.value,mod,remainder_value,List.length_replicate]
@[simp] theorem capPow_number (P Q C : Expr n) (v : Env n) :
    (capPow P Q C).number v=min (P.number v^Q.number v) (C.number v) := by
  simp only [Expr.number,Expr.value,capPow,boundedPower_value,List.length_replicate]
@[simp] theorem eq_value (P Q : Expr n) (v : Env n) : (eq P Q).value v=[decide (P.number v=Q.number v)] :=
  equal_value ..
@[simp] theorem le_value (P Q : Expr n) (v : Env n) : (le P Q).value v=[decide (P.number v≤Q.number v)] :=
  lessEq_value ..
@[simp] theorem choose_value (B P Q : Expr n) (v : Env n) :
    (choose B P Q).value v=if B.bit v then P.value v else Q.value v := by
  simp only [Expr.value,Expr.bit,choose,Recipe.choose_value]
  by_cases h : (B.program.value v).head?=some true <;> simp [h]
@[simp] theorem neg_value (P : Expr n) (v : Env n) : (neg P).value v=[!(P.bit v)] := by
  rw [neg,choose_value,literal_value,literal_value]
  cases P.bit v <;> rfl
@[simp] theorem lt_value (P Q : Expr n) (v : Env n) : (lt P Q).value v=[decide (P.number v<Q.number v)] := by
  simp only [lt,neg_value,Expr.bit,le_value,List.head?_cons,Option.some.injEq,decide_bool]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp
 theorem bit_singleton (P : Expr n) (v : Env n) (b : Bool) (h : P.value v=[b]) : P.bit v=b := by
  unfold Expr.bit
  simp only [h,List.head?_cons,Option.some.injEq,decide_bool]

@[simp] theorem eq_bit (P Q : Expr n) (v : Env n) : (eq P Q).bit v=decide (P.number v=Q.number v) := bit_singleton _ _ _ (eq_value P Q v)
@[simp] theorem le_bit (P Q : Expr n) (v : Env n) : (le P Q).bit v=decide (P.number v≤Q.number v) := bit_singleton _ _ _ (le_value P Q v)
@[simp] theorem lt_bit (P Q : Expr n) (v : Env n) : (lt P Q).bit v=decide (P.number v<Q.number v) := bit_singleton _ _ _ (lt_value P Q v)
@[simp] theorem neg_bit (P : Expr n) (v : Env n) : (neg P).bit v=!(P.bit v) := bit_singleton _ _ _ (neg_value P v)
@[simp] theorem conj_value (P Q : Expr n) (v : Env n) : (conj P Q).value v=[P.bit v && Q.bit v] := Recipe.conj_value ..
@[simp] theorem conj_bit (P Q : Expr n) (v : Env n) : (conj P Q).bit v=(P.bit v && Q.bit v) := bit_singleton _ _ _ (conj_value P Q v)
@[simp] theorem choose_bit (B P Q : Expr n) (v : Env n) :
    (choose B P Q).bit v=if B.bit v then P.bit v else Q.bit v := by
  change decide (((choose B P Q).value v).head?=some true)=_
  rw [choose_value]
  split <;> rfl
@[simp] theorem bitEq_bit (P Q : Expr n) (v : Env n) : (bitEq P Q).bit v=decide (P.bit v=Q.bit v) := by
  rw [bitEq,choose_bit,neg_bit]
  cases P.bit v <;> cases Q.bit v <;> rfl
@[simp] theorem lookup_value (P Q : Expr n) (v : Env n) : (lookup P Q).value v=[(P.value v).getD (Q.number v) false] :=
  atIndex_value ..
@[simp] theorem lookup_bit (P Q : Expr n) (v : Env n) : (lookup P Q).bit v=(P.value v).getD (Q.number v) false := bit_singleton _ _ _ (lookup_value P Q v)
@[simp] theorem all_value (B : Expr n) (Q : Expr (n+1)) (v : Env n) :
    (all B Q).value v=[(List.range (B.number v)).all (fun i=>Q.bit (cons (List.replicate i true) v))] := Recipe.all_value ..
@[simp] theorem all_bit (B : Expr n) (Q : Expr (n+1)) (v : Env n) :
    (all B Q).bit v=(List.range (B.number v)).all (fun i=>Q.bit (cons (List.replicate i true) v)) := bit_singleton _ _ _ (all_value B Q v)
@[simp] theorem collect_value (B : Expr n) (Q : Expr (n+1)) (v : Env n) :
    (collect B Q).value v=(List.range (B.number v)).map (fun i=>Q.bit (cons (List.replicate i true) v)) := Recipe.collect_value ..
@[simp] theorem count_number (B : Expr n) (Q : Expr (n+1)) (v : Env n) :
    (count B Q).number v=(List.range (B.number v)).countP (fun i=>Q.bit (cons (List.replicate i true) v)) := by
  simp only [Expr.number,Expr.value,count,countTrue_value,List.length_replicate]
  rfl

end PolyRecipe
end VariableWL.Computation.Stack

end OAI
