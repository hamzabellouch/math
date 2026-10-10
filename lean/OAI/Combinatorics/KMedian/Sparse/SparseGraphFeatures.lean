import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseMarginalTools
import OAI.Combinatorics.KMedian.Sparse.SparseProduct
import OAI.Combinatorics.KMedian.Sparse.SparseMomentAlgebra

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

abbrev Graph (n m : ℕ) := Fin m → Finset (Fin n)

def edge (G : Graph n m) (h : Fin n) (i : Fin m) : ℚ := if h ∈ G i then 1 else 0

def edgeCode (G : Graph n m) (a : Fin (n*m)) : ℚ :=
  edge G (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2

def features (G : Graph n m) (a : Fin (n*m+(n*m)*(n*m))) : ℚ :=
  Sum.elim (edgeCode G) (fun ij : Fin ((n*m)*(n*m)) =>
    edgeCode G (finProdFinEquiv.symm ij).1*edgeCode G (finProdFinEquiv.symm ij).2)
    (finSumFinEquiv.symm a)

@[simp] theorem features_single (G : Graph n m) (h : Fin n) (i : Fin m) :
    features G (finSumFinEquiv (Sum.inl (finProdFinEquiv (h,i))))=edge G h i := by
  simp only [features,edgeCode,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] theorem features_pair (G : Graph n m) (h k : Fin n) (i j : Fin m) :
    features G (finSumFinEquiv (Sum.inr (finProdFinEquiv
      (finProdFinEquiv (h,i),finProdFinEquiv (k,j)))))=edge G h i*edge G k j := by
  simp only [features,edgeCode,Equiv.symm_apply_apply,Sum.elim_inr]

def next (G : Graph n m) (S : Finset (Fin n)) (i : Fin m) : Graph n m :=
  Function.update G i S

@[simp] theorem edge_next (G : Graph n m) (S : Finset (Fin n)) (h : Fin n) (i j : Fin m) :
    edge (next G S i) h j=if j=i then (if h∈S then 1 else 0) else edge G h j := by
  by_cases hji : j=i <;> simp [edge,next,hji]

def step (μ : SparseIntegerLaw (Graph n m)) (ν : SparseIntegerLaw (Finset (Fin n)))
    (i : Fin m) : SparseIntegerLaw (Graph n m) :=
  μ.prodCompress ν (fun G S => next G S i) features

theorem step_single (μ : SparseIntegerLaw (Graph n m)) (ν : SparseIntegerLaw (Finset (Fin n)))
    (i j : Fin m) (h : Fin n) :
    (step μ ν i).moment (fun G => edge G h j)=
      if j=i then ν.moment (fun S => if h∈S then 1 else 0) else μ.moment (fun G => edge G h j) := by
  have hh := (μ.prodCompress_spec ν (fun G S => next G S i) features).2.2
    (finSumFinEquiv (Sum.inl (finProdFinEquiv (h,j))))
  simp only [features_single] at hh
  refine hh.trans ?_
  by_cases hji : j=i
  · simp only [edge_next,ite_eq_left hji]
    exact μ.moment_const _
  · simp only [edge_next,ite_eq_right hji]
    simp only [SparseIntegerLaw.moment_const]

theorem step_pair (μ : SparseIntegerLaw (Graph n m)) (ν : SparseIntegerLaw (Finset (Fin n)))
    (i j k : Fin m) (h l : Fin n) (hjk : j≠k) :
    (step μ ν i).moment (fun G => edge G h j*edge G l k)=
      if j=i then ν.moment (fun S => if h∈S then 1 else 0)*μ.moment (fun G => edge G l k)
      else if k=i then μ.moment (fun G => edge G h j)*ν.moment (fun S => if l∈S then 1 else 0)
      else μ.moment (fun G => edge G h j*edge G l k) := by
  have hh := (μ.prodCompress_spec ν (fun G S => next G S i) features).2.2
    (finSumFinEquiv (Sum.inr (finProdFinEquiv (finProdFinEquiv (h,j),finProdFinEquiv (l,k)))))
  simp only [features_pair] at hh
  refine hh.trans ?_
  by_cases hji : j=i
  · have hki : k≠i := fun hk => hjk (hji.trans hk.symm)
    simp only [edge_next,ite_eq_left hji,ite_eq_right hki,
      SparseIntegerLaw.moment_mul_right,SparseIntegerLaw.moment_mul]
  · by_cases hki : k=i
    · simp only [edge_next,ite_eq_right hji,ite_eq_left hki,
        SparseIntegerLaw.moment_mul,SparseIntegerLaw.moment_mul_right]
    · simp only [edge_next,ite_eq_right hji,ite_eq_right hki,SparseIntegerLaw.moment_const]

end MetricKMedian.SparseGraph
end
end

end OAI
