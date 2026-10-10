import Mathlib
import OAI.Analysis.MatrixSigning.Machines.Realification
import OAI.Analysis.MatrixSigning.Matrices.Space

namespace OAI

namespace CurrentKS.HermitianCoordinates
open Matrix
open scoped BigOperators

variable {d : ℕ}

def realDecode {R : Type*} [Ring R] (x : Fin d × Fin d → R) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R :=
  let re := fun i j => x (min i j,max i j)
  let im := fun i j => if i < j then x (j,i) else if j < i then -x (i,j) else 0
  Matrix.fromBlocks re (-im) im re

private lemma realDecode_inl_inl {R : Type*} [Ring R]
    (x : Fin d × Fin d → R) (i j : Fin d) :
    realDecode x (Sum.inl i) (Sum.inl j) = x (min i j, max i j) := rfl

private lemma realDecode_inl_inr {R : Type*} [Ring R]
    (x : Fin d × Fin d → R) (i j : Fin d) :
    realDecode x (Sum.inl i) (Sum.inr j) =
      -(if i < j then x (j, i) else if j < i then -x (i, j) else 0) := rfl

private lemma realDecode_inr_inl {R : Type*} [Ring R]
    (x : Fin d × Fin d → R) (i j : Fin d) :
    realDecode x (Sum.inr i) (Sum.inl j) =
      (if i < j then x (j, i) else if j < i then -x (i, j) else 0) := rfl

private lemma realDecode_inr_inr {R : Type*} [Ring R]
    (x : Fin d × Fin d → R) (i j : Fin d) :
    realDecode x (Sum.inr i) (Sum.inr j) = x (min i j, max i j) := rfl

lemma realDecode_isSymm {R : Type*} [Ring R] (x : Fin d × Fin d → R) :
    (realDecode x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [realDecode_inl_inl,min_comm,max_comm]
    | inr j =>
      rcases lt_trichotomy i j with h | h | h
      · simp [realDecode_inl_inr, realDecode_inr_inl,h,not_lt.mpr h.le]
      · subst j; simp [realDecode_inl_inr, realDecode_inr_inl]
      · simp [realDecode_inl_inr, realDecode_inr_inl,h,not_lt.mpr h.le]
  | inr i =>
    cases j with
    | inl j =>
      rcases lt_trichotomy i j with h | h | h
      · simp [realDecode_inl_inr, realDecode_inr_inl,h,not_lt.mpr h.le]
      · subst j; simp [realDecode_inl_inr, realDecode_inr_inl]
      · simp [realDecode_inl_inr, realDecode_inr_inl,h,not_lt.mpr h.le]
    | inr j => simp [realDecode_inr_inr,min_comm,max_comm]

lemma realDecode_eq_realify (x : Fin d × Fin d → ℝ) :
    realDecode x = KS.W08.realify (decode x) := by
  ext i j
  cases i <;> cases j <;> rfl

lemma realDecode_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (x : Fin d × Fin d → R) : (realDecode x).map f=realDecode (f ∘ x) := by
  ext i j
  cases i <;> cases j <;>
    simp only [realDecode_inl_inl, realDecode_inl_inr, realDecode_inr_inl, realDecode_inr_inr, Matrix.map_apply,
      Function.comp_def,map_neg]
  all_goals split_ifs <;> simp only [map_neg,map_zero]

lemma realDecode_add {R : Type*} [Ring R] (x y : Fin d × Fin d → R) :
    realDecode (x+y)=realDecode x+realDecode y := by
  ext i j
  cases i <;> cases j <;> simp [realDecode_inl_inl, realDecode_inl_inr, realDecode_inr_inl, realDecode_inr_inr] <;> split_ifs <;> abel

lemma realDecode_smul {R : Type*} [CommRing R] (r : R) (x : Fin d × Fin d → R) :
    realDecode (r • x)=r • realDecode x := by
  ext i j
  cases i <;> cases j <;> simp [realDecode_inl_inl, realDecode_inl_inr, realDecode_inr_inl, realDecode_inr_inr]

def realDecodeLinear {R : Type*} [CommRing R] (d : ℕ) :
    (Fin d × Fin d → R) →ₗ[R] Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R where
  toFun := realDecode
  map_add' := realDecode_add
  map_smul' := realDecode_smul

lemma realDecode_ratCast (x : Fin d × Fin d → ℚ) :
    (realDecode x).map (fun q => (q:ℝ))=realDecode (fun i => (x i:ℝ)) :=
  realDecode_map (algebraMap ℚ ℝ) x
end CurrentKS.HermitianCoordinates

end OAI
