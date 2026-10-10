import OAI.Combinatorics.VariableWL.PolyRecipe

namespace OAI

namespace VariableWL.NumericProgram
open Computation.Stack Computation.Stack.Recipe Computation.Stack.PolyRecipe
variable {n m : ℕ}

@[simp] theorem cons_one (w z : Word) (v : Env n) : cons z (cons w v) (1 : Fin (n+2))=w := rfl

structure Data (n : ℕ) where
  leftOrder : Expr n
  rightOrder : Expr n
  dimension : Expr n
  leftMatrix : Expr n
  rightMatrix : Expr n
  capacity : Expr n

def Data.reindex (D : Data n) (φ : Fin n → Fin m) : Data m :=
  ⟨D.leftOrder.reindex φ,D.rightOrder.reindex φ,D.dimension.reindex φ,
    D.leftMatrix.reindex φ,D.rightMatrix.reindex φ,D.capacity.reindex φ⟩
def Data.up (D : Data n) : Data (n+1) := D.reindex Fin.succ
def Data.up₂ (D : Data n) : Data (n+2) := D.reindex (fun i=>i.succ.succ)
def Data.eval (D : Data n) (v : Env n) : NumericRefinement.Data :=
  ⟨D.leftOrder.number v,D.rightOrder.number v,D.dimension.number v,D.leftMatrix.value v,D.rightMatrix.value v⟩
def Data.Good (D : Data n) (v : Env n) : Prop :=
  1≤D.capacity.number v ∧ D.leftOrder.number v^D.dimension.number v≤D.capacity.number v ∧
    D.rightOrder.number v^D.dimension.number v≤D.capacity.number v
@[simp] theorem eval_reindex (D : Data n) (φ : Fin n → Fin m) (v : Env m) :
    (D.reindex φ).eval v=D.eval (v ∘ φ) := rfl
@[simp] theorem eval_up (D : Data n) (v : Env n) (w : Word) : D.up.eval (cons w v)=D.eval v := rfl
@[simp] theorem eval_up₂ (D : Data n) (v : Env n) (w z : Word) : D.up₂.eval (cons z (cons w v))=D.eval v := rfl
 theorem good_up {D : Data n} {v : Env n} (h : D.Good v) (w : Word) : D.up.Good (cons w v) := h
 theorem good_up₂ {D : Data n} {v : Env n} (h : D.Good v) (w z : Word) : D.up₂.Good (cons z (cons w v)) := h

@[simp] theorem choose_number (B P Q : Expr n) (v : Env n) :
    (PolyRecipe.choose B P Q).number v=if B.bit v then P.number v else Q.number v := by
  unfold Expr.number
  rw [PolyRecipe.choose_value]
  split <;> rfl
@[simp] theorem up_bit (P : Expr n) (v : Env n) (w : Word) : P.up.bit (cons w v)=P.bit v := rfl
@[simp] theorem up₂_bit (P : Expr n) (v : Env n) (w z : Word) : P.up₂.bit (cons z (cons w v))=P.bit v := rfl

 theorem power_bound (a i k C : ℕ) (hi : i≤k) (h1 : 1≤C) (h : a^k≤C) : a^i≤C := by
  by_cases ha : a=0
  · subst a
    by_cases hz : i=0
    · simpa [hz] using h1
    · simp [zero_pow hz]
  · exact (Nat.pow_le_pow_right (Nat.pos_of_ne_zero ha) hi).trans h

def Data.leftCount (D : Data n) : Expr n := capPow D.leftOrder D.dimension D.capacity
def Data.rightCount (D : Data n) : Expr n := capPow D.rightOrder D.dimension D.capacity
def Data.count (D : Data n) : Expr n := add D.leftCount D.rightCount
def Data.isLeft (D : Data n) (a : Expr n) : Expr n := lt a D.leftCount
def Data.order (D : Data n) (a : Expr n) : Expr n := PolyRecipe.choose (D.isLeft a) D.leftOrder D.rightOrder
def Data.offset (D : Data n) (a : Expr n) : Expr n := PolyRecipe.choose (D.isLeft a) (numeral 0) D.leftCount
def Data.power (D : Data n) (a i : Expr n) : Expr n := capPow (D.order a) i D.capacity
def Data.coordinate (D : Data n) (a i : Expr n) : Expr n := mod (div (sub a (D.offset a)) (D.power a i)) (D.order a)
def Data.replacement (D : Data n) (a z i : Expr n) : Expr n :=
  add (D.offset a) (add (sub (sub a (D.offset a)) (mul (D.coordinate a i) (D.power a i))) (mul z (D.power a i)))
def Data.edge (D : Data n) (a i j : Expr n) : Expr n :=
  PolyRecipe.lookup (PolyRecipe.choose (D.isLeft a) D.leftMatrix D.rightMatrix)
    (add (mul (D.coordinate a i) (D.order a)) (D.coordinate a j))

theorem leftCount_number (D : Data n) (v : Env n) (h : D.Good v) :
    D.leftCount.number v=(D.eval v).leftCount := by
  rw [Data.leftCount,capPow_number,min_eq_left h.2.1]
  rfl
theorem rightCount_number (D : Data n) (v : Env n) (h : D.Good v) :
    D.rightCount.number v=(D.eval v).rightCount := by
  rw [Data.rightCount,capPow_number,min_eq_left h.2.2]
  rfl
theorem count_number (D : Data n) (v : Env n) (h : D.Good v) :
    D.count.number v=(D.eval v).count := by
  rw [Data.count,add_number,leftCount_number _ _ h,rightCount_number _ _ h]
  rfl
theorem isLeft_bit (D : Data n) (a : Expr n) (v : Env n) (h : D.Good v) :
    (D.isLeft a).bit v=(D.eval v).isLeft (a.number v) := by
  rw [Data.isLeft,PolyRecipe.lt_bit,leftCount_number _ _ h]
  rfl
theorem order_number (D : Data n) (a : Expr n) (v : Env n) (h : D.Good v) :
    (D.order a).number v=(D.eval v).order (a.number v) := by
  rw [Data.order,choose_number,isLeft_bit _ _ _ h]
  rfl
theorem offset_number (D : Data n) (a : Expr n) (v : Env n) (h : D.Good v) :
    (D.offset a).number v=(D.eval v).offset (a.number v) := by
  rw [Data.offset,choose_number,isLeft_bit _ _ _ h,numeral_number,leftCount_number _ _ h]
  rfl
theorem power_number (D : Data n) (a i : Expr n) (v : Env n) (h : D.Good v)
    (hi : i.number v≤D.dimension.number v) :
    (D.power a i).number v=(D.eval v).order (a.number v)^i.number v := by
  rw [Data.power,capPow_number,order_number _ _ _ h]
  apply min_eq_left
  unfold NumericRefinement.Data.order
  split
  · exact power_bound _ _ _ _ hi h.1 h.2.1
  · exact power_bound _ _ _ _ hi h.1 h.2.2

theorem coordinate_number (D : Data n) (a i : Expr n) (v : Env n) (h : D.Good v)
    (hi : i.number v≤D.dimension.number v) :
    (D.coordinate a i).number v=(D.eval v).coordinate (a.number v) (i.number v) := by
  rw [Data.coordinate,mod_number,div_number,sub_number,offset_number _ _ _ h,
    power_number _ _ _ _ h hi,order_number _ _ _ h]
  rfl

theorem replacement_number (D : Data n) (a z i : Expr n) (v : Env n) (h : D.Good v)
    (hi : i.number v≤D.dimension.number v) :
    (D.replacement a z i).number v=(D.eval v).replacement (a.number v) (z.number v) (i.number v) := by
  simp only [Data.replacement,add_number,sub_number,mul_number,offset_number _ _ _ h,
    coordinate_number _ _ _ _ h hi,power_number _ _ _ _ h hi]
  rfl

theorem edge_bit (D : Data n) (a i j : Expr n) (v : Env n) (h : D.Good v)
    (hi : i.number v≤D.dimension.number v) (hj : j.number v≤D.dimension.number v) :
    (D.edge a i j).bit v=(D.eval v).edge (a.number v) (i.number v) (j.number v) := by
  rw [Data.edge,lookup_bit,PolyRecipe.choose_value,isLeft_bit _ _ _ h,add_number,mul_number,
    coordinate_number _ _ _ _ h hi,coordinate_number _ _ _ _ h hj,order_number _ _ _ h]
  rfl

def Data.initial (D : Data n) (a b : Expr n) : Expr n :=
  PolyRecipe.all D.dimension (PolyRecipe.all D.up.dimension
    (PolyRecipe.conj (bitEq (PolyRecipe.eq (D.up₂.coordinate a.up₂ (PolyRecipe.input 1)) (D.up₂.coordinate a.up₂ (PolyRecipe.input 0)))
      (PolyRecipe.eq (D.up₂.coordinate b.up₂ (PolyRecipe.input 1)) (D.up₂.coordinate b.up₂ (PolyRecipe.input 0))))
      (bitEq (D.up₂.edge a.up₂ (PolyRecipe.input 1) (PolyRecipe.input 0))
        (D.up₂.edge b.up₂ (PolyRecipe.input 1) (PolyRecipe.input 0)))))

theorem list_all_congr {α : Type} (xs : List α) {f g : α → Bool} (h : ∀a∈xs,f a=g a) : xs.all f=xs.all g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.all_cons,List.all_cons,h a (by simp),ih (by intro b hb; exact h b (by simp [hb]))]

theorem initial_bit (D : Data n) (a b : Expr n) (v : Env n) (h : D.Good v) :
    (D.initial a b).bit v=(D.eval v).initial (a.number v) (b.number v) := by
  rw [Data.initial,all_bit]
  unfold NumericRefinement.Data.initial
  apply list_all_congr
  intro i hi
  rw [all_bit]
  change (List.range (D.dimension.number v)).all _=_
  apply list_all_congr
  intro j hj
  have hi' : (PolyRecipe.input (1 : Fin (n+2))).number (cons (List.replicate j true) (cons (List.replicate i true) v))≤
      D.up₂.dimension.number (cons (List.replicate j true) (cons (List.replicate i true) v)) := by
    change (List.replicate i true).length≤D.dimension.number v
    simpa only [List.length_replicate] using Nat.le_of_lt (List.mem_range.mp hi)
  have hj' : (PolyRecipe.input (0 : Fin (n+2))).number (cons (List.replicate j true) (cons (List.replicate i true) v))≤
      D.up₂.dimension.number (cons (List.replicate j true) (cons (List.replicate i true) v)) := by
    change (List.replicate j true).length≤D.dimension.number v
    simpa only [List.length_replicate] using Nat.le_of_lt (List.mem_range.mp hj)
  simp only [conj_bit,bitEq_bit,eq_bit,coordinate_number _ _ _ _ (good_up₂ h _ _) hi',
    coordinate_number _ _ _ _ (good_up₂ h _ _) hj',edge_bit _ _ _ _ _ (good_up₂ h _ _) hi' hj',
    eval_up₂,up₂_number,input_number,cons_one,cons_zero,List.length_replicate]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]

end VariableWL.NumericProgram

namespace VariableWL.NumericProgram
open Computation.Stack Computation.Stack.Recipe Computation.Stack.PolyRecipe
variable {n : ℕ}

def sameRanges (A B : Expr n) (AA AB BA BB : Expr (n+2)) : Expr n :=
  PolyRecipe.conj
    (PolyRecipe.all A (PolyRecipe.eq (PolyRecipe.count A.up AA) (PolyRecipe.count B.up AB)))
    (PolyRecipe.all B (PolyRecipe.eq (PolyRecipe.count A.up BA) (PolyRecipe.count B.up BB)))

theorem sameRanges_bit (A B : Expr n) (AA AB BA BB : Expr (n+2)) (v : Env n) :
    (sameRanges A B AA AB BA BB).bit v=
      (((List.range (A.number v)).all fun x=>decide
        ((List.range (A.number v)).countP (fun y=>AA.bit (cons (List.replicate y true) (cons (List.replicate x true) v)))=
         (List.range (B.number v)).countP (fun y=>AB.bit (cons (List.replicate y true) (cons (List.replicate x true) v))))) &&
      ((List.range (B.number v)).all fun x=>decide
        ((List.range (A.number v)).countP (fun y=>BA.bit (cons (List.replicate y true) (cons (List.replicate x true) v)))=
         (List.range (B.number v)).countP (fun y=>BB.bit (cons (List.replicate y true) (cons (List.replicate x true) v)))))) := by
  simp only [sameRanges,conj_bit,all_bit,eq_bit,PolyRecipe.count_number,up_number]

theorem sameCounts_ranges {α : Type} (e : α → α → Bool) (A B : ℕ) (f g : ℕ → α) :
    RefinementTable.sameCounts e ((List.range A).map f) ((List.range B).map g)=
      (((List.range A).all fun x=>decide ((List.range A).countP (fun y=>e (f x) (f y))=
        (List.range B).countP (fun y=>e (f x) (g y)))) &&
      ((List.range B).all fun x=>decide ((List.range A).countP (fun y=>e (g x) (f y))=
        (List.range B).countP (fun y=>e (g x) (g y))))) := by
  simp only [RefinementTable.sameCounts,List.all_append,List.all_map,List.filter_map,List.length_map,
    Function.comp_def,List.countP_eq_length_filter]

def Data.get (D : Data n) (R a b : Expr n) : Expr n := PolyRecipe.lookup R (add (mul a D.count) b)
def Data.profile (D : Data n) (R a z b w : Expr n) : Expr n :=
  PolyRecipe.all D.dimension (D.up.get R.up (D.up.replacement a.up z.up (PolyRecipe.input 0))
    (D.up.replacement b.up w.up (PolyRecipe.input 0)))
def Data.comparison (D : Data n) (R a b : Expr n) : Expr n :=
  sameRanges (D.order a) (D.order b)
    (D.up₂.profile R.up₂ a.up₂ (PolyRecipe.input 1) a.up₂ (PolyRecipe.input 0))
    (D.up₂.profile R.up₂ a.up₂ (PolyRecipe.input 1) b.up₂ (PolyRecipe.input 0))
    (D.up₂.profile R.up₂ b.up₂ (PolyRecipe.input 1) a.up₂ (PolyRecipe.input 0))
    (D.up₂.profile R.up₂ b.up₂ (PolyRecipe.input 1) b.up₂ (PolyRecipe.input 0))
def Data.update (D : Data n) (R a b : Expr n) : Expr n := PolyRecipe.conj (D.get R a b) (D.comparison R a b)

theorem get_bit (D : Data n) (R a b : Expr n) (v : Env n) (h : D.Good v) :
    (D.get R a b).bit v=(D.eval v).get (R.value v) (a.number v) (b.number v) := by
  rw [Data.get,lookup_bit,add_number,mul_number,count_number _ _ h]
  rfl

theorem profile_bit (D : Data n) (R a z b w : Expr n) (v : Env n) (h : D.Good v) :
    (D.profile R a z b w).bit v=(D.eval v).profile (R.value v) (a.number v,z.number v) (b.number v,w.number v) := by
  rw [Data.profile,all_bit]
  unfold NumericRefinement.Data.profile
  apply list_all_congr
  intro i hi
  have hi' : (PolyRecipe.input (0 : Fin (n+1))).number (cons (List.replicate i true) v)≤D.up.dimension.number (cons (List.replicate i true) v) := by
    change (List.replicate i true).length≤D.dimension.number v
    simpa only [List.length_replicate] using Nat.le_of_lt (List.mem_range.mp hi)
  rw [get_bit _ _ _ _ _ (good_up h _),replacement_number _ _ _ _ _ (good_up h _) hi',
    replacement_number _ _ _ _ _ (good_up h _) hi']
  simp only [eval_up,up_value,up_number,input_number,cons_zero,List.length_replicate]

theorem comparison_bit (D : Data n) (R a b : Expr n) (v : Env n) (h : D.Good v) :
    (D.comparison R a b).bit v=RefinementTable.sameCounts ((D.eval v).profile (R.value v))
      ((D.eval v).neighbors (a.number v)) ((D.eval v).neighbors (b.number v)) := by
  rw [Data.comparison,sameRanges_bit]
  unfold NumericRefinement.Data.neighbors
  rw [sameCounts_ranges]
  simp only [order_number _ _ _ h,profile_bit _ _ _ _ _ _ _ (good_up₂ h _ _),
    eval_up₂,up₂_value,up₂_number,input_number,cons_one,cons_zero,List.length_replicate]

theorem update_bit (D : Data n) (R a b : Expr n) (v : Env n) (h : D.Good v) :
    (D.update R a b).bit v=(D.eval v).update (R.value v) (a.number v) (b.number v) := by
  rw [Data.update,conj_bit,get_bit _ _ _ _ _ h,comparison_bit _ _ _ _ _ h]
  rfl

def Data.initialArray (D : Data n) : Expr n :=
  PolyRecipe.collect (mul D.count D.count)
    (D.up.initial (div (PolyRecipe.input 0) D.up.count) (mod (PolyRecipe.input 0) D.up.count))
def Data.nextArray (D : Data n) (R : Expr n) : Expr n :=
  PolyRecipe.collect (mul D.count D.count)
    (D.up.update R.up (div (PolyRecipe.input 0) D.up.count) (mod (PolyRecipe.input 0) D.up.count))

theorem initialArray_value (D : Data n) (v : Env n) (h : D.Good v) :
    D.initialArray.value v=(D.eval v).array 0 := by
  rw [Data.initialArray,PolyRecipe.collect_value]
  simp only [mul_number,count_number _ _ h,initial_bit _ _ _ _ (good_up h _),
    eval_up,div_number,mod_number,input_number,cons_zero,List.length_replicate,count_number _ _ (good_up h _)]
  rfl

theorem nextArray_value (D : Data n) (R : Expr n) (v : Env n) (h : D.Good v) :
    (D.nextArray R).value v=(D.eval v).pack ((D.eval v).update (R.value v)) := by
  rw [Data.nextArray,PolyRecipe.collect_value]
  simp only [mul_number,count_number _ _ h,update_bit _ _ _ _ _ (good_up h _),
    eval_up,up_value,div_number,mod_number,input_number,cons_zero,List.length_replicate,count_number _ _ (good_up h _)]
  rfl

end VariableWL.NumericProgram

namespace VariableWL.NumericProgram
open Computation.Stack Computation.Stack.Recipe Computation.Stack.PolyRecipe
variable {n : ℕ}

theorem count_up₂ (D : Data n) (v : Env n) (w z : Word) :
    D.up₂.count.number (cons z (cons w v))=D.count.number v := by
  simp only [Data.count,add_number,Data.leftCount,Data.rightCount,capPow_number]
  rfl

theorem initialArray_length (D : Data n) (v : Env n) :
    (D.initialArray.value v).length=D.count.number v^2 := by
  rw [Data.initialArray,PolyRecipe.collect_value,List.length_map,List.length_range,mul_number,pow_two]

theorem nextArray_length (D : Data n) (R : Expr n) (v : Env n) :
    ((D.nextArray R).value v).length=D.count.number v^2 := by
  rw [Data.nextArray,PolyRecipe.collect_value,List.length_map,List.length_range,mul_number,pow_two]

def Data.arrayBody (D : Data n) : Expr (n+2) := D.up₂.nextArray (PolyRecipe.input 0)
def Data.arrayProgram (D : Data n) : Certified n :=
  Recipe.iterate (mul D.count D.count).program D.initialArray.program D.arrayBody.program

theorem arrayPrefix_length (D : Data n) (v : Env n) (j : ℕ) :
    (Recipe.foldValue D.arrayBody.program v (D.initialArray.value v) j).length=D.count.number v^2 := by
  cases j with
  | zero => exact initialArray_length D v
  | succ j =>
    change ((D.up₂.nextArray (PolyRecipe.input 0)).value _).length=_
    rw [nextArray_length,count_up₂]

theorem arrayProgram_poly (D : Data n) : Poly D.arrayProgram := by
  obtain ⟨f,hf,h⟩ := D.count.polynomial
  apply Recipe.poly_iterate (mul D.count D.count).polynomial D.initialArray.polynomial D.arrayBody.polynomial
    (fun C=>(f C)^2) (hf.pow 2)
  intro C v hv j hj
  change (Recipe.foldValue D.arrayBody.program v (D.initialArray.value v) j).length≤(f C)^2
  rw [arrayPrefix_length]
  have hb := h C v hv
  exact Nat.pow_le_pow_left (show D.count.number v≤f C by exact (Nat.le_add_left _ _).trans hb) 2

def Data.array (D : Data n) : Expr n := ⟨D.arrayProgram,arrayProgram_poly D⟩

theorem arrayPrefix_value (D : Data n) (v : Env n) (h : D.Good v) (j : ℕ) :
    Recipe.foldValue D.arrayBody.program v (D.initialArray.value v) j=(D.eval v).array j := by
  induction j with
  | zero => exact initialArray_value D v h
  | succ j ih =>
    change (D.up₂.nextArray (PolyRecipe.input 0)).value _=_
    rw [nextArray_value _ _ _ (good_up₂ h _ _)]
    simp only [eval_up₂,PolyRecipe.input_value,cons_zero,ih]
    rfl

theorem array_value (D : Data n) (v : Env n) (h : D.Good v) :
    D.array.value v=(D.eval v).array ((D.eval v).count^2) := by
  change (Recipe.iterate (mul D.count D.count).program D.initialArray.program D.arrayBody.program).value v=_
  rw [Recipe.iterate_value]
  change Recipe.foldValue D.arrayBody.program v (D.initialArray.value v) ((mul D.count D.count).number v)=_
  rw [arrayPrefix_value _ _ h]
  rw [mul_number,count_number _ _ h,pow_two]

def Data.histogram (D : Data n) (R : Expr n) : Expr n :=
  sameRanges D.leftCount D.rightCount
    (D.up₂.get R.up₂ (PolyRecipe.input 1) (PolyRecipe.input 0))
    (D.up₂.get R.up₂ (PolyRecipe.input 1) (add D.up₂.leftCount (PolyRecipe.input 0)))
    (D.up₂.get R.up₂ (add D.up₂.leftCount (PolyRecipe.input 1)) (PolyRecipe.input 0))
    (D.up₂.get R.up₂ (add D.up₂.leftCount (PolyRecipe.input 1)) (add D.up₂.leftCount (PolyRecipe.input 0)))

theorem histogram_bit (D : Data n) (R : Expr n) (v : Env n) (h : D.Good v) :
    (D.histogram R).bit v=(D.eval v).histogram (R.value v) := by
  rw [Data.histogram,sameRanges_bit]
  unfold NumericRefinement.Data.histogram
  have hs := sameCounts_ranges ((D.eval v).get (R.value v)) (D.eval v).leftCount (D.eval v).rightCount id ((D.eval v).leftCount+·)
  rw [List.map_id] at hs
  rw [hs]
  simp only [leftCount_number _ _ h,rightCount_number _ _ h,get_bit _ _ _ _ _ (good_up₂ h _ _),
    add_number,leftCount_number _ _ (good_up₂ h _ _),eval_up₂,up₂_value,input_number,cons_one,cons_zero,List.length_replicate,id_eq]

theorem sameRanges_singleton (A B : Expr n) (AA AB BA BB : Expr (n+2)) (v : Env n) :
    (sameRanges A B AA AB BA BB).value v=[(sameRanges A B AA AB BA BB).bit v] := by
  rw [sameRanges,PolyRecipe.conj_value,conj_bit]

def Data.accepts (D : Data n) : Expr n := D.histogram D.array

theorem accepts_value (D : Data n) (v : Env n) (h : D.Good v) :
    D.accepts.value v=[(D.eval v).accepts] := by
  change (sameRanges _ _ _ _ _ _).value _=_
  rw [sameRanges_singleton]
  change [(D.histogram D.array).bit v]=_
  rw [histogram_bit _ _ _ h,array_value _ _ h]
  rfl

theorem accepts_correct (D : Data n) (v : Env n) (h : D.Good v) (G H : Graph) (k : ℕ)
    (hv : D.eval v=NumericRefinement.data G H k) :
    D.accepts.value v=[true] ↔ Equivalent G H k := by
  rw [accepts_value _ _ h,hv,List.cons.injEq]
  simp only [and_true]
  exact NumericRefinement.accepts_correct G H k

end VariableWL.NumericProgram

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def Expr.bind (P : Expr n) (Q : Expr (n+1)) : Expr n :=
  ⟨P.program.bind Q.program,poly_bind P.polynomial Q.polynomial⟩
@[simp] theorem bind_value (P : Expr n) (Q : Expr (n+1)) (v : Env n) :
    (P.bind Q).value v=Q.value (cons (P.value v) v) := rfl

def length (P : Expr n) : Expr n := ⟨Recipe.len P.program,poly_len P.polynomial⟩
def reverse (P : Expr n) : Expr n := ⟨Recipe.rev P.program,poly_rev P.polynomial⟩
def drop (P Q : Expr n) : Expr n := ⟨tailAt P.program Q.program,poly_tailAt P.polynomial Q.polynomial⟩
def minimum (P Q : Expr n) : Expr n := ⟨Recipe.minimum P.program Q.program,poly_minimum P.polynomial Q.polynomial⟩
def append (P Q : Expr n) : Expr n := ⟨cat P.program Q.program,poly_cat P.polynomial Q.polynomial⟩
@[simp] theorem length_number (P : Expr n) (v : Env n) : (length P).number v=(P.value v).length := by
  simp only [Expr.number,Expr.value,length,len_value,List.length_replicate]
@[simp] theorem reverse_value (P : Expr n) (v : Env n) : (reverse P).value v=(P.value v).reverse := Recipe.rev_value ..
@[simp] theorem drop_value (P Q : Expr n) (v : Env n) : (drop P Q).value v=(P.value v).drop (Q.number v) := tailAt_value ..
@[simp] theorem minimum_value (P Q : Expr n) (v : Env n) :
    (minimum P Q).value v=List.replicate (min (P.number v) (Q.number v)) true := Recipe.minimum_value ..
@[simp] theorem minimum_number (P Q : Expr n) (v : Env n) : (minimum P Q).number v=min (P.number v) (Q.number v) := by
  unfold Expr.number
  rw [minimum_value,List.length_replicate]
  rfl
@[simp] theorem append_value (P Q : Expr n) (v : Env n) : (append P Q).value v=P.value v++Q.value v := cat_value ..

def foldWordIndices (n : ℕ) : Fin (n+2) → Fin (n+3) :=
  Fin.cons 1 (Fin.cons 0 (fun i=>i.succ.succ.succ))

theorem foldWord_env (v : Env n) (acc bit index : Word) :
    cons bit (cons acc (cons index v)) ∘ foldWordIndices n=cons acc (cons bit v) := by
  funext i
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>?_) i) i <;> rfl

def foldWordBody (W : Expr n) (Q : Expr (n+2)) : Expr (n+2) :=
  (lookup W.up₂ (input 1)).bind (Q.reindex (foldWordIndices n))

theorem foldWordBody_value (W : Expr n) (Q : Expr (n+2)) (v : Env n) (acc : Word) (i : ℕ) :
    (foldWordBody W Q).value (cons acc (cons (List.replicate i true) v))=
      Q.value (cons acc (cons [(W.value v).getD i false] v)) := by
  rw [foldWordBody,bind_value,reindex_value,lookup_value,up₂_value,input_number]
  change Q.value (cons [(W.value v).getD (List.replicate i true).length false]
    (cons acc (cons (List.replicate i true) v)) ∘ foldWordIndices n)=_
  rw [List.length_replicate,foldWord_env]

def foldWordStep (Q : Expr (n+2)) (v : Env n) (a : Word) (b : Bool) : Word := Q.value (cons a (cons [b] v))

theorem foldWord_prefix (W Z : Expr n) (Q : Expr (n+2)) (v : Env n) (j : ℕ) (hj : j≤(W.value v).length) :
    foldValue (foldWordBody W Q).program v (Z.value v) j=
      ((W.value v).take j).foldl (foldWordStep Q v) (Z.value v) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j<(W.value v).length := by omega
    change (foldWordBody W Q).value (cons (foldValue (foldWordBody W Q).program v (Z.value v) j)
      (cons (List.replicate j true) v))=_
    rw [foldWordBody_value,ih (by omega),List.take_succ_eq_append_getElem hj',List.foldl_append,List.foldl_cons,List.foldl_nil]
    unfold foldWordStep
    rw [List.getD_eq_getElem _ _ hj']

def foldWordProgram (W Z : Expr n) (Q : Expr (n+2)) : Certified n :=
  Recipe.iterate (length W).program Z.program (foldWordBody W Q).program

theorem foldWordProgram_value (W Z : Expr n) (Q : Expr (n+2)) (v : Env n) :
    (foldWordProgram W Z Q).value v=(W.value v).foldl (foldWordStep Q v) (Z.value v) := by
  rw [foldWordProgram,Recipe.iterate_value]
  change foldValue (foldWordBody W Q).program v (Z.value v) ((length W).number v)=_
  rw [length_number,foldWord_prefix _ _ _ _ _ le_rfl,List.take_length]

theorem foldWordProgram_poly (W Z : Expr n) (Q : Expr (n+2)) (F : ℕ → ℕ) (hF : Growth F)
    (hacc : ∀C v,EnvBound C v → ∀j≤(W.value v).length,
      (((W.value v).take j).foldl (foldWordStep Q v) (Z.value v)).length≤F C) :
    Poly (foldWordProgram W Z Q) := by
  apply poly_iterate (length W).polynomial Z.polynomial (foldWordBody W Q).polynomial F hF
  intro C v hv j hj
  change j≤(length W).number v at hj
  rw [length_number] at hj
  change (foldValue (foldWordBody W Q).program v (Z.value v) j).length≤F C
  rw [foldWord_prefix _ _ _ _ _ hj]
  exact hacc C v hv j hj

end VariableWL.Computation.Stack.PolyRecipe

end OAI
