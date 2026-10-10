import Mathlib
import OAI.GroupTheory.SimpleOvergroups.FiniteNames
import OAI.GroupTheory.SimpleOvergroups.PolynomialBounds
import OAI.GroupTheory.SimpleOvergroups.PolynomialNames
import OAI.GroupTheory.SimpleOvergroups.TruncatedMatrix

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.MatrixNames
open BoundedEncoding
noncomputable section
open scoped Classical
variable {A k : Type*} [CommRing k] {n : ℕ}
abbrev Column (k A : Type*) (n : ℕ) := Fin n → Polynomial.Name k A
abbrev Name (k A : Type*) (n : ℕ) := Fin n → Column k A n
abbrev Raw (k A : Type*) [CommRing k] := MonoidAlgebra k (FreeMonoid A)

def columnValue (x : Column k A n) : Fin n → Raw k A := fun i => Polynomial.value (x i)
def value (a : Name k A n) : Matrix (Fin n) (Fin n) (Raw k A) := fun i => columnValue (a i)

def maximum (f : Fin n → ℕ) : ℕ := (List.ofFn f).foldr max 0

theorem maximum_le_iff (f : Fin n → ℕ) (b : ℕ) : maximum f ≤ b ↔ ∀ i, f i ≤ b := by
  suffices h : ∀ l : List ℕ, l.foldr max 0 ≤ b ↔ ∀ x ∈ l, x ≤ b by
    simp only [maximum,h,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]
  intro l
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons,max_le_iff,ih,List.mem_cons,forall_eq_or_imp]

 theorem le_maximum (f : Fin n → ℕ) (i : Fin n) : f i ≤ maximum f :=
  (maximum_le_iff f _).mp le_rfl i

def columnCost (grade : List A → ℕ) (x : Column k A n) := maximum (fun i => Polynomial.cost grade (x i))
def cost (grade : List A → ℕ) (a : Name k A n) := maximum (fun i => columnCost grade (a i))

omit [CommRing k] in
 theorem entry_cost_le (grade : List A → ℕ) (a : Name k A n) (i j : Fin n) :
    Polynomial.cost grade (a i j) ≤ cost grade a :=
  (le_maximum (fun j => Polynomial.cost grade (a i j)) j).trans
    (le_maximum (fun i => columnCost grade (a i)) i)

omit [CommRing k] in
 theorem column_entry_cost_le (grade : List A → ℕ) (x : Column k A n) (i : Fin n) :
    Polynomial.cost grade (x i) ≤ columnCost grade x := le_maximum (fun i => Polynomial.cost grade (x i)) i

def oneName : Name k A n := fun i j => if i=j then Polynomial.oneName else []

def product (a b : Name k A n) : Name k A n :=
  fun i j => (List.ofFn (fun l => Polynomial.product (a i l) (b l j))).flatten

def mulVec (a : Name k A n) (x : Column k A n) : Column k A n :=
  fun i => (List.ofFn (fun j => Polynomial.product (a i j) (x j))).flatten

@[simp] theorem value_oneName : value (oneName : Name k A n) = 1 := by
  funext i j
  by_cases h : i=j <;> simp [value,columnValue,oneName,Matrix.one_apply,h]

@[simp] theorem value_product (a b : Name k A n) : value (product a b) = value a * value b := by
  ext i j
  simp only [value,columnValue,product,Polynomial.value_flatten,List.map_ofFn,
    Polynomial.value_product,Function.comp_def,List.sum_ofFn,Matrix.mul_apply]

@[simp] theorem value_mulVec (a : Name k A n) (x : Column k A n) :
    columnValue (mulVec a x) = (value a).mulVec (columnValue x) := by
  ext i
  simp only [value,columnValue,mulVec,Polynomial.value_flatten,List.map_ofFn,
    Polynomial.value_product,Function.comp_def,List.sum_ofFn,Matrix.mulVec,dotProduct]

 theorem cost_oneName (grade : List A → ℕ) (h0 : grade [] = 0) :
    cost grade (oneName : Name k A n) = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [cost,maximum_le_iff]
  intro i
  rw [columnCost,maximum_le_iff]
  intro j
  by_cases h : i=j <;> simp [oneName,h,Polynomial.cost_oneName grade h0]

 theorem cost_product_le (grade : List A → ℕ)
    (ha : ∀ u v, grade (u++v) = grade u + grade v) (a b : Name k A n) :
    cost grade (product a b) ≤ cost grade a + cost grade b := by
  rw [cost,maximum_le_iff]
  intro i
  rw [columnCost,maximum_le_iff]
  intro j
  apply Polynomial.cost_flatten_le
  intro p hp
  obtain ⟨l,rfl⟩ := List.mem_ofFn.mp hp
  exact (Polynomial.cost_product_le grade ha _ _).trans
    (Nat.add_le_add (entry_cost_le _ a i l) (entry_cost_le _ b l j))

 theorem cost_mulVec_le (grade : List A → ℕ)
    (ha : ∀ u v, grade (u++v) = grade u + grade v) (a : Name k A n) (x : Column k A n) :
    columnCost grade (mulVec a x) ≤ cost grade a + columnCost grade x := by
  rw [columnCost,maximum_le_iff]
  intro i
  apply Polynomial.cost_flatten_le
  intro p hp
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
  exact (Polynomial.cost_product_le grade ha _ _).trans
    (Nat.add_le_add (entry_cost_le _ a i j) (column_entry_cost_le _ x j))

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
 theorem mem_ball (a : Name k A n) :
    C.MatrixBall k (cost (fun w => C.grade (FreeMonoid.ofList w)) a) (value a) :=
  fun i j => C.ball_mono k (entry_cost_le _ a i j) (Polynomial.mem_ball C (a i j))

 theorem column_mem_ball (x : Column k A n) :
    C.ColumnBall k (columnCost (fun w => C.grade (FreeMonoid.ofList w)) x) (columnValue x) :=
  fun i => C.ball_mono k (column_entry_cost_le _ x i) (Polynomial.mem_ball C (x i))

variable [Primcodable A] [Primcodable k] [Finite k]

 theorem primrec_maximum : Primrec (maximum (n:=n)) := by
  unfold maximum
  exact Primrec.list_foldr (Primrec.list_ofFn (fun i => Primrec.fin_app.comp Primrec.id (Primrec.const i)))
    (Primrec.const 0) (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

omit [CommRing k] [Finite k] in
 theorem primrec_columnCost {grade : List A → ℕ} (hg : Primrec grade) :
    Primrec (columnCost (k:=k) (n:=n) grade) :=
  primrec_maximum.comp (Finite.primrec_function fun i =>
    (Polynomial.primrec_cost hg).comp (Primrec.fin_app.comp Primrec.id (Primrec.const i)))

omit [CommRing k] [Finite k] in
 theorem primrec_cost {grade : List A → ℕ} (hg : Primrec grade) :
    Primrec (cost (k:=k) (n:=n) grade) :=
  primrec_maximum.comp (Finite.primrec_function fun i =>
    (primrec_columnCost hg).comp (Primrec.fin_app.comp Primrec.id (Primrec.const i)))

 theorem primrec_product : Primrec₂ (product (k:=k) (A:=A) (n:=n)) := by
  apply Finite.primrec_function
  intro i
  apply Finite.primrec_function
  intro j
  exact Primrec.list_flatten.comp (Primrec.list_ofFn fun l => Polynomial.primrec_product.comp
    (Primrec.fin_app.comp (Primrec.fin_app.comp Primrec.fst (Primrec.const i)) (Primrec.const l))
    (Primrec.fin_app.comp (Primrec.fin_app.comp Primrec.snd (Primrec.const l)) (Primrec.const j)))

 theorem primrec_mulVec : Primrec₂ (mulVec (k:=k) (A:=A) (n:=n)) := by
  apply Finite.primrec_function
  intro i
  exact Primrec.list_flatten.comp (Primrec.list_ofFn fun j => Polynomial.primrec_product.comp
    (Primrec.fin_app.comp (Primrec.fin_app.comp Primrec.fst (Primrec.const i)) (Primrec.const j))
    (Primrec.fin_app.comp Primrec.snd (Primrec.const j)))

def columnKey (x : Fin n → Raw k A) : Fin n → ℕ := fun i => Polynomial.valueKey (x i)
def matrixKey (a : Matrix (Fin n) (Fin n) (Raw k A)) : Fin n → Fin n → ℕ :=
  fun i => columnKey (a i)

omit [Finite k] in
 theorem columnKey_injective : Function.Injective (columnKey (k:=k) (A:=A) (n:=n)) := by
  intro x y h
  funext i
  exact Polynomial.valueKey_injective (congrFun h i)

omit [Finite k] in
 theorem matrixKey_injective : Function.Injective (matrixKey (k:=k) (A:=A) (n:=n)) := by
  intro x y h
  funext i
  exact columnKey_injective (congrFun h i)

def partialColumnKey (omega : List A) (f : List A → Part (List A)) (x : Column k A n) :
    Part (Fin n → ℕ) := Finite.traverse (Polynomial.partialKey omega f) x

def partialMatrixKey (omega : List A) (f : List A → Part (List A)) (a : Name k A n) :
    Part (Fin n → Fin n → ℕ) := Finite.traverse (partialColumnKey omega f) a

omit [Finite k] in
 theorem partialColumnKey_full (f : List A → Part (List A)) (x : Column k A n) {d : ℕ}
    (hx : columnCost (fun w => C.grade (FreeMonoid.ofList w)) x ≤ d)
    (h : ∀ w, C.grade (FreeMonoid.ofList w) ≤ d → (C.normal (FreeMonoid.ofList w)).toList ∈ f w) :
    columnKey (C.columnCollect k (columnValue x)) ∈ partialColumnKey C.omega.toList f x := by
  apply Finite.traverse_full (Polynomial.partialKey C.omega.toList f)
    (fun p => Polynomial.valueKey (C.collect k (Polynomial.value p))) x
  intro i
  apply Polynomial.partialKey_full C
  intro a ha
  exact h a.2 ((Polynomial.term_cost_le _ ha).trans ((column_entry_cost_le _ x i).trans hx))

omit [Finite k] in
 theorem partialMatrixKey_full (f : List A → Part (List A)) (a : Name k A n) {d : ℕ}
    (hx : cost (fun w => C.grade (FreeMonoid.ofList w)) a ≤ d)
    (h : ∀ w, C.grade (FreeMonoid.ofList w) ≤ d → (C.normal (FreeMonoid.ofList w)).toList ∈ f w) :
    matrixKey (C.matrixCollect k (value a)) ∈ partialMatrixKey C.omega.toList f a := by
  apply Finite.traverse_full (partialColumnKey C.omega.toList f)
    (fun x => columnKey (C.columnCollect k (columnValue x))) a
  intro i
  exact partialColumnKey_full C f (a i) ((le_maximum (fun i => columnCost (fun w => C.grade (FreeMonoid.ofList w)) (a i)) i).trans hx) h

variable {P : Type*} [Primcodable P] {f : P → List A → Part (List A)}

 theorem partrec_partialColumnKey (omega : List A) (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => partialColumnKey (k:=k) (n:=n) omega (f p)) :=
  Finite.partrec_traverse (Polynomial.partrec_partialKey omega hf)

 theorem partrec_partialMatrixKey (omega : List A) (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => partialMatrixKey (k:=k) (n:=n) omega (f p)) :=
  Finite.partrec_traverse (partrec_partialColumnKey omega hf)

end
end SimpleFInftyOvergroups.EffectiveNames.MatrixNames

end OAI
