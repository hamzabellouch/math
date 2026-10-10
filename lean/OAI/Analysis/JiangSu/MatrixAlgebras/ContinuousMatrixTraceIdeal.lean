import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Weights
import OAI.Analysis.JiangSu.CStarAlgebras.ContinuousRadialFactor

namespace OAI

section

noncomputable section
namespace ContinuousMatrixTraceIdeal
variable {X I : Type*} [TopologicalSpace X] [Fintype I] [DecidableEq I]

abbrev PathMatrix := C(X,Matrix I I ℂ)

def single (i j : I) (z : C(X,ℂ)) : PathMatrix (X := X) (I := I) :=
  ⟨fun x => Matrix.single i j (z x), by
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    by_cases hrow : i = row <;> by_cases hcolumn : j = column <;>
      simp [Matrix.single, hrow, hcolumn, continuous_const, z.continuous]⟩

lemma single_mul (i j k : I) (z w : C(X,ℂ)) :
    single i j z*single j k w=single i k (z*w) := by
  ext x a b
  exact congrFun (congrFun (Matrix.single_mul_single_same (z x) i j k (w x)) a) b

lemma single_mul_zero (i j k l : I) (hjk : j≠k) (z w : C(X,ℂ)) :
    single i j z*single k l w=0 := by
  ext x a b
  exact congrFun (congrFun (Matrix.single_mul_single_of_ne (z x) i j k hjk (w x)) a) b

omit [Fintype I] in
lemma single_vanishes (i j : I) {z : C(X,ℂ)} {E : Set X} (hz : ∀ x∈E,z x=0) :
    ∀ x∈E,single i j z x=0 := by
  intro x hx
  change Matrix.single i j (z x)=0
  rw [hz x hx,Matrix.single_zero]

variable (T : PathMatrix (X := X) (I := I) →ₗ[ℂ] ℂ) (E : Set X)
variable (hT : ∀ u v : PathMatrix (X := X) (I := I),
  (∀ x∈E,u x=0) → (∀ x∈E,v x=0) → T (u*v)=T (v*u))

include hT in
lemma diagonal_equal (z : C(X,ℂ)) (hz : ∀ x∈E,z x=0) (i j : I) :
    T (single i i z)=T (single j j z) := by
  obtain ⟨g,h,hgh,hzero⟩ := ContinuousRadialFactor.exists_factorization z
  have hg : ∀ x∈E,g x=0 := fun x hx => (hzero x (hz x hx)).1
  have hh : ∀ x∈E,h x=0 := fun x hx => (hzero x (hz x hx)).2
  have he := hT (single i j g) (single j i h)
    (single_vanishes _ _ hg) (single_vanishes _ _ hh)
  rw [single_mul,single_mul,hgh,mul_comm h g,hgh] at he
  exact he

include hT in
lemma offdiagonal_zero (z : C(X,ℂ)) (hz : ∀ x∈E,z x=0) (i j : I) (hij : i≠j) :
    T (single i j z)=0 := by
  obtain ⟨g,h,hgh,hzero⟩ := ContinuousRadialFactor.exists_factorization z
  have hg : ∀ x∈E,g x=0 := fun x hx => (hzero x (hz x hx)).1
  have hh : ∀ x∈E,h x=0 := fun x hx => (hzero x (hz x hx)).2
  have he := hT (single i i g) (single i j h)
    (single_vanishes _ _ hg) (single_vanishes _ _ hh)
  rw [single_mul,hgh,single_mul_zero _ _ _ _ hij.symm,map_zero] at he
  exact he

def entry (f : PathMatrix (X := X) (I := I)) (i j : I) : C(X,ℂ) :=
  ⟨fun x => f x i j,by fun_prop⟩

def tracePath (f : PathMatrix (X := X) (I := I)) : C(X,ℂ) :=
  ∑ i, entry f i i

lemma decompose (f : PathMatrix (X := X) (I := I)) : f=∑ i,∑ j,single i j (entry f i j) := by
  apply ContinuousMap.ext
  intro x
  simp only [ContinuousMap.sum_apply]
  exact Matrix.matrix_eq_sum_single (f x)

include hT in
lemma eval_as_single_trace (k : I) (f : PathMatrix (X := X) (I := I))
    (hf : ∀ x∈E,f x=0) : T f=T (single k k (tracePath f)) := by
  have he (i j : I) : ∀ x∈E,entry f i j x=0 := by
    intro x hx
    change f x i j=0
    rw [hf x hx]; rfl
  have hentry (i j : I) : T (single i j (entry f i j))=
      if i=j then T (single k k (entry f i i)) else 0 := by
    split_ifs with h
    · subst j
      exact diagonal_equal T E hT _ (he i i) i k
    · exact offdiagonal_zero T E hT _ (he i j) i j h
  calc
    T f=∑ i,∑ j,T (single i j (entry f i j)) := by
      conv_lhs => rw [decompose f]
      simp only [map_sum]
    _=∑ i,T (single k k (entry f i i)) := by
      simp only [hentry, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    _=T (∑ i,single k k (entry f i i)) := (map_sum _ _ _).symm
    _=T (single k k (tracePath f)) := by
      congr 1
      ext x a b
      simp only [ContinuousMap.sum_apply,tracePath,single,entry,ContinuousMap.coe_mk]
      exact congrFun
        (congrFun ((map_sum (Matrix.singleLinearMap ℂ k k) _ _).symm) a) b

def scalarPath (z : C(X,ℂ)) : PathMatrix (X := X) (I := I) :=
  ⟨fun x => z x • (1 : Matrix I I ℂ),by fun_prop⟩

lemma tracePath_scalar (z : C(X,ℂ)) :
    tracePath (scalarPath (I := I) z)=(Fintype.card I : ℂ) • z := by
  ext x
  simp [tracePath,entry,scalarPath]

include hT in

theorem scalarization [Nonempty I] (f : PathMatrix (X := X) (I := I))
    (hf : ∀ x∈E,f x=0) :
    T f=T (scalarPath ((Fintype.card I : ℂ)⁻¹ • tracePath f)) := by
  let k : I := Classical.arbitrary I
  rw [eval_as_single_trace T E hT k f hf]
  symm
  rw [eval_as_single_trace T E hT k _ (by
    intro x hx
    simp [scalarPath,tracePath,entry,hf x hx])]
  congr 2
  rw [tracePath_scalar,smul_smul]
  have hn : (Fintype.card I : ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_inv_cancel₀ hn,one_smul]

end ContinuousMatrixTraceIdeal

end
end

end OAI
