import Mathlib
import OAI.GroupTheory.SimpleOvergroups.MatrixNames
import OAI.GroupTheory.SimpleOvergroups.NamedActions
import OAI.GroupTheory.SimpleOvergroups.PolynomialBounds

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.MatrixWords
open BoundedEncoding MatrixNames
noncomputable section
open scoped Classical
variable {A k : Type*} [CommRing k] {n : ℕ}

abbrev Root (k A : Type*) (n : ℕ) := Fin n × Fin n × Polynomial.Name k A
abbrev Word (k A : Type*) (n : ℕ) := List (Root k A n)
abbrev Point (k A : Type*) (n : ℕ) := Word k A n × Column k A n
abbrev V (k A : Type*) [CommRing k] (n : ℕ) := (Matrix (Fin n) (Fin n) (Raw k A))ˣ

def rootInv (r : Root k A n) : Root k A n := (r.1,r.2.1,Polynomial.negate r.2.2)
def inverse (w : Word k A n) : Word k A n := w.reverse.map rootInv

def rootValue (r : Root k A n) : V k A n :=
  if h : r.1 ≠ r.2.1 then FiniteAlgebraicEnvelopes.Steinberg.elementary r.1 r.2.1 h (Polynomial.value r.2.2)
  else 1

def groupValue (w : Word k A n) : V k A n := (w.map rootValue).prod

@[simp] theorem groupValue_nil : groupValue ([] : Word k A n) = 1 := rfl
@[simp] theorem groupValue_cons (r : Root k A n) (w : Word k A n) :
    groupValue (r::w) = rootValue r * groupValue w := rfl
@[simp] theorem groupValue_append (a b : Word k A n) :
    groupValue (a++b) = groupValue a * groupValue b := by simp [groupValue]

@[simp] theorem rootValue_inv (r : Root k A n) : rootValue (rootInv r) = (rootValue r)⁻¹ := by
  by_cases h : r.1 ≠ r.2.1
  · simp only [rootValue,rootInv,dite_eq_left h,Polynomial.value_negate]
    apply Units.ext
    simp only [FiniteAlgebraicEnvelopes.Steinberg.elementary_val,
      FiniteAlgebraicEnvelopes.Steinberg.elementary_inv_val,
      Matrix.single_neg,sub_eq_add_neg]
  · simp [rootValue,rootInv,h]

@[simp] theorem inverse_nil : inverse ([] : Word k A n) = [] := rfl
@[simp] theorem inverse_cons (r : Root k A n) (w : Word k A n) :
    inverse (r::w) = inverse w ++ [rootInv r] := by simp [inverse]

@[simp] theorem groupValue_inverse (w : Word k A n) : groupValue (inverse w) = (groupValue w)⁻¹ := by
  induction w with
  | nil => simp
  | cons r w ih => simp [ih,mul_inv_rev]

def gcost (grade : List A → ℕ) (w : Word k A n) : ℕ :=
  (w.map (fun r => Polynomial.cost grade r.2.2)).sum

def xcost (grade : List A → ℕ) (x : Point k A n) : ℕ :=
  gcost grade x.1 + columnCost grade x.2

omit [CommRing k] in
@[simp] theorem gcost_nil [CommRing k] (grade : List A → ℕ) : gcost grade ([] : Word k A n) = 0 := rfl
omit [CommRing k] in
@[simp] theorem gcost_cons [CommRing k] (grade : List A → ℕ) (r : Root k A n) (w : Word k A n) :
    gcost grade (r::w) = Polynomial.cost grade r.2.2 + gcost grade w := rfl
omit [CommRing k] in
@[simp] theorem gcost_append [CommRing k] (grade : List A → ℕ) (a b : Word k A n) :
    gcost grade (a++b) = gcost grade a + gcost grade b := by simp [gcost]
@[simp] theorem gcost_inverse (grade : List A → ℕ) (w : Word k A n) :
    gcost grade (inverse w) = gcost grade w := by
  simp [gcost,inverse,List.map_map,Function.comp_def,rootInv]

def nameOperations (grade : List A → ℕ) : NamedAction.Operations (Word k A n) (Point k A n) where
  one := []
  mul := (·++·)
  inv := inverse
  act := fun g x => (g++x.1,x.2)
  gcost := gcost grade
  xcost := xcost grade
  cost_one := rfl
  cost_mul := gcost_append grade
  cost_inv := gcost_inverse grade
  cost_act := by intros; simp [xcost,gcost_append,Nat.add_assoc]

attribute [local instance] WordCalculus.rawMatrixAction

def pointValue (x : Point k A n) : Fin n → Raw k A := groupValue x.1 • columnValue x.2

@[simp] theorem pointValue_act (g : Word k A n) (x : Point k A n) :
    pointValue (g++x.1,x.2) = groupValue g • pointValue x := by
  simp only [pointValue,groupValue_append,mul_smul]

def rootMatrix (r : Root k A n) : Name k A n := fun i j =>
  oneName i j ++ if r.1 ≠ r.2.1 ∧ r.1=i ∧ r.2.1=j then r.2.2 else []

def matrix (w : Word k A n) : Name k A n := w.foldr (fun r a => product (rootMatrix r) a) oneName

def column (x : Point k A n) : Column k A n := mulVec (matrix x.1) x.2

@[simp] theorem value_rootMatrix (r : Root k A n) : value (rootMatrix r) = (rootValue r).val := by
  funext i j
  change Polynomial.value (oneName i j ++ _) = _
  rw [Polynomial.value_append]
  have hh : Polynomial.value (oneName (k:=k) (A:=A) i j) = (1 : Matrix (Fin n) (Fin n) (Raw k A)) i j :=
    congrFun (congrFun value_oneName i) j
  rw [hh]
  by_cases h : r.1 ≠ r.2.1
  · simp only [rootValue,dite_eq_left h,FiniteAlgebraicEnvelopes.Steinberg.elementary_val,
      Matrix.add_apply,Matrix.single_apply]
    by_cases he : r.1=i ∧ r.2.1=j
    · rw [ite_eq_left ⟨h,he⟩,ite_eq_left he]
    · rw [ite_eq_right (fun hh => he hh.2),ite_eq_right he]
      rfl
  · simp [rootValue,h]

@[simp] theorem value_matrix (w : Word k A n) : value (matrix w) = (groupValue w).val := by
  induction w with
  | nil => exact value_oneName
  | cons r w ih =>
    change value (product (rootMatrix r) (matrix w)) = _
    simp only [value_product,value_rootMatrix,ih,groupValue_cons,Units.val_mul]

@[simp] theorem value_column (x : Point k A n) : columnValue (column x) = pointValue x := by
  simp only [column,value_mulVec,value_matrix]
  rfl

 theorem cost_rootMatrix (grade : List A → ℕ) (h0 : grade [] = 0) (r : Root k A n) :
    cost grade (rootMatrix r) ≤ Polynomial.cost grade r.2.2 := by
  rw [cost,maximum_le_iff]
  intro i
  rw [columnCost,maximum_le_iff]
  intro j
  change Polynomial.cost grade (oneName i j ++ _) ≤ _
  rw [Polynomial.cost_append,max_le_iff]
  constructor
  · have hh := entry_cost_le grade (oneName : Name k A n) i j
    rw [cost_oneName grade h0] at hh
    omega
  · split_ifs <;> simp

 theorem cost_matrix (grade : List A → ℕ) (h0 : grade [] = 0)
    (ha : ∀ u v, grade (u++v) = grade u + grade v) (w : Word k A n) :
    cost grade (matrix w) ≤ gcost grade w := by
  induction w with
  | nil => simpa [matrix] using (cost_oneName (k:=k) (n:=n) grade h0).le
  | cons r w ih =>
    change cost grade (product (rootMatrix r) (matrix w)) ≤
      Polynomial.cost grade r.2.2 + gcost grade w
    exact (cost_product_le grade ha _ _).trans (Nat.add_le_add (cost_rootMatrix grade h0 r) ih)

 theorem cost_column (grade : List A → ℕ) (h0 : grade [] = 0)
    (ha : ∀ u v, grade (u++v) = grade u + grade v) (x : Point k A n) :
    columnCost grade (column x) ≤ xcost grade x :=
  (cost_mulVec_le grade ha _ _).trans
    (Nat.add_le_add_right (cost_matrix grade h0 ha x.1) _)

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)

def grade (w : List A) : ℕ := C.grade (FreeMonoid.ofList w)

@[simp] theorem grade_nil : grade C [] = 0 := C.grade_one
@[simp] theorem grade_append (u v : List A) : grade C (u++v) = grade C u + grade C v := C.grade_mul _ _

 theorem groupValue_mem (w : Word k A n) : C.UnitBall k (gcost (grade C) w) (groupValue w) := by
  constructor
  · rw [← value_matrix]
    exact fun i j => C.ball_mono k (cost_matrix (grade C) (grade_nil C) (grade_append C) w)
      (MatrixNames.mem_ball C (matrix w) i j)
  · change C.MatrixBall k (gcost (grade C) w) (groupValue w)⁻¹.val
    rw [← groupValue_inverse,← value_matrix]
    have hh := cost_matrix (grade C) (grade_nil C) (grade_append C) (inverse w)
    rw [gcost_inverse] at hh
    exact fun i j => C.ball_mono k hh (MatrixNames.mem_ball C (matrix (inverse w)) i j)

 theorem pointValue_mem (x : Point k A n) : C.ColumnBall k (xcost (grade C) x) (pointValue x) := by
  rw [← value_column]
  exact fun i => C.ball_mono k (cost_column (grade C) (grade_nil C) (grade_append C) x)
    (column_mem_ball C (column x) i)

end
end SimpleFInftyOvergroups.EffectiveNames.MatrixWords

end OAI
