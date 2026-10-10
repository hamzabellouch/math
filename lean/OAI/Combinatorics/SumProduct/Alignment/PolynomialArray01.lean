import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice15
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
end

section
 

 

noncomputable section
open scoped BigOperators
namespace PolynomialArrayInterpolation
open CorrectedBoxLeibman MvPolynomial WeightedPolynomial
open IntegerGridInterpolation (tensorWeight tensor_orthogonality)
abbrev Grid := IntegerGridInterpolation.Grid

lemma bounded_totalDegree {q d : ℕ} {p : MvPolynomial (Fin q) ℝ}
    (hp : Bounded (fun _ : Fin q=>1) d p) : p.totalDegree≤d := by
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro e he
  have hh:=hp e (MvPolynomial.mem_support_iff.mp he)
  simpa only [Finsupp.weight_apply,smul_eq_mul,mul_one] using hh

lemma real_orthogonality (q d : ℕ) (e f : Grid q d) :
    ∑ v : Grid q d,(tensorWeight q d e v:ℝ)*∏ i,((v i).val:ℝ)^(f i).val=
      if e=f then 1 else 0 := by
  have hh:=congrArg (fun x : ℚ => (x:ℝ)) (tensor_orthogonality q d e f)
  push_cast at hh
  split_ifs at hh ⊢ <;> simpa only [Rat.cast_one,Rat.cast_zero] using hh

lemma reconstruction (q d : ℕ) (a : Grid q d → ℝ) (e : Grid q d) :
    ∑ v : Grid q d,(tensorWeight q d e v:ℝ)*
      (∑ f : Grid q d,a f*∏ i,((v i).val:ℝ)^(f i).val)=a e := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_left_comm (tensorWeight q d e _:ℝ) (a _)]
  simp_rw [← Finset.mul_sum,real_orthogonality]
  simp

def coefficients {q d : ℕ} (f : (Fin q → ℝ) → ℝ) (e : Grid q d) : ℝ:=
  ∑ v : Grid q d,(tensorWeight q d e v:ℝ)*f (fun i=>((v i).val:ℝ))

lemma coefficients_eval {q d : ℕ} (p : MvPolynomial (Fin q) ℝ) (hp : p.totalDegree≤d)
    (e : Grid q d) : coefficients (fun x=>eval x p) e=polynomialGrid p e := by
  unfold coefficients
  simp_rw [← gridEval_polynomial p hp]
  exact reconstruction q d (polynomialGrid p) e

lemma reconstruction_function {q d : ℕ} {f : (Fin q → ℝ) → ℝ}
    (hf : IsWeighted (fun _ : Fin q=>1) d f) (x : Fin q → ℝ) :
    gridEval (coefficients f : Grid q d → ℝ) x=f x := by
  obtain ⟨p,hp,he⟩:=hf
  have htd:=bounded_totalDegree hp
  have hf : f=fun x=>eval x p:=funext he
  rw [hf]
  have hc : (coefficients (fun x=>eval x p) : Grid q d → ℝ)=polynomialGrid p :=
    funext (coefficients_eval p htd)
  rw [hc]
  exact gridEval_polynomial p htd x

lemma coefficients_zero_high {q d : ℕ} {f : (Fin q → ℝ) → ℝ} {k : ℕ}
    (hf : IsWeighted (fun _ : Fin q=>1) k f) (hkd : k≤d) (e : Grid q d)
    (he : k<PolynomialLineCoefficients.totalDegree e) : coefficients f e=0 := by
  obtain ⟨p,hp,hf⟩:=hf
  have htd:=bounded_totalDegree hp
  have hfun : f=fun x=>eval x p:=funext hf
  rw [hfun,coefficients_eval p (htd.trans hkd)]
  change p.coeff (gridExponent e)=0
  by_contra hn
  have hh:=hp (gridExponent e) hn
  have hd : Finsupp.weight (fun _ : Fin q=>1) (gridExponent e)=PolynomialLineCoefficients.totalDegree e := by
    rw [Finsupp.weight_apply]
    simpa only [smul_eq_mul,mul_one] using gridExponent_degree e
  rw [hd] at hh
  omega

lemma coefficients_continuous {q d : ℕ} (e : Grid q d) :
    Continuous (fun f : ((Fin q → ℝ) → ℝ)=>coefficients f e) := by
  apply continuous_finsetSum
  intro v hv
  exact continuous_const.mul (continuous_apply _)

lemma gridEval_weighted {q d k : ℕ} (a : Grid q d → ℝ)
    (ha : ∀ e,k<PolynomialLineCoefficients.totalDegree e → a e=0) :
    IsWeighted (fun _ : Fin q=>1) k (gridEval a) := by
  classical
  refine ⟨∑ e : Grid q d,monomial (gridExponent e) (a e),?_,?_⟩
  · apply bounded_sum
    intro e he m hm
    have hme : gridExponent e=m := by
      by_contra h
      simp only [coeff_monomial,h,ite_false] at hm
      exact hm rfl
    subst m
    have hae : a e≠0 := by simpa only [coeff_monomial,ite_true] using hm
    have hd : Finsupp.weight (fun _ : Fin q=>1) (gridExponent e)=
        PolynomialLineCoefficients.totalDegree e := by
      rw [Finsupp.weight_apply]
      simpa only [smul_eq_mul,mul_one] using gridExponent_degree e
    rw [hd]
    by_contra h
    exact hae (ha e (Nat.lt_of_not_ge h))
  · intro x
    simp only [gridEval,map_sum,eval_monomial]
    apply Finset.sum_congr rfl
    intro e he
    congr 1
    rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
    rfl

lemma coefficients_gridEval {q d : ℕ} (a : Grid q d → ℝ) (e : Grid q d) :
    coefficients (gridEval a) e=a e := reconstruction q d a e

lemma grid_injective {q d : ℕ} {f g : (Fin q → ℝ) → ℝ}
    (hf : IsWeighted (fun _ : Fin q=>1) d f)
    (hg : IsWeighted (fun _ : Fin q=>1) d g)
    (hfg : ∀ v : Grid q d,f (fun i=>((v i).val:ℝ))=g (fun i=>((v i).val:ℝ))) : f=g := by
  have hc : (coefficients f : Grid q d → ℝ)=coefficients g := by
    funext e
    simp only [coefficients,hfg]
  funext x
  rw [← reconstruction_function hf x,← reconstruction_function hg x,hc]

end PolynomialArrayInterpolation
end
 
end

section
 

 
noncomputable section
namespace SortedFiniteWeights
variable {σ : Type*} [Fintype σ]
lemma exists_ordered (w : σ → ℕ) :
    ∃ e : Fin (Fintype.card σ) ≃ σ,Monotone (fun i=>w (e i)) := by
  classical
  let f (i : σ) : ℕ ×ₗ Fin (Fintype.card σ):=toLex (w i,Fintype.equivFin σ i)
  have hf : Function.Injective f := by
    intro i j h
    apply (Fintype.equivFin σ).injective
    exact congrArg (fun x=> (ofLex x).2) h
  let : LinearOrder σ:=LinearOrder.lift' f hf
  let e:=Fintype.orderIsoFinOfCardEq σ rfl
  refine ⟨e.toEquiv,?_⟩
  intro i j hij
  have hh : f (e i) ≤ f (e j):=e.monotone hij
  rcases Prod.Lex.le_iff.mp hh with h|h
  · exact Nat.le_of_lt h
  · exact le_of_eq h.1

def indexing (w : σ → ℕ) : Fin (Fintype.card σ) ≃ σ:=(exists_ordered w).choose
lemma indexing_monotone (w : σ → ℕ) : Monotone (fun i=>w (indexing w i)) :=
  (exists_ordered w).choose_spec

end SortedFiniteWeights
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalLattice.PolynomialArrays
open PolynomialArrayInterpolation WeightedPolynomial MalcevCharacters
open CorrectedBoxLeibman (gridEval)
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n q : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i : Fin n,w i<k → c.coord g i=0)

abbrev Index (w : Fin n → ℕ) (q : ℕ) :=
  Σ i : Fin n,{e : Grid q (w i) // PolynomialLineCoefficients.totalDegree e≤w i}

def fullCoeff (x : Index w q → ℝ) (i : Fin n) (e : Grid q (w i)) : ℝ :=
  if he : PolynomialLineCoefficients.totalDegree e≤w i then x ⟨i,⟨e,he⟩⟩ else 0

def toLog (x : Index w q → ℝ) (u : Fin q → ℝ) (i : Fin n) : ℝ :=
  gridEval (fullCoeff w x i) u

omit [IsTopologicalGroup G] in
lemma toLog_array (x : Index w q → ℝ) :
    IsArray c w (fun u=>canonicalExp c (toLog w x u)) := by
  intro i
  simp only [canonicalLog_exp]
  apply gridEval_weighted
  intro e he
  simp only [fullCoeff,dite_eq_right (not_le.mpr he)]

def coefficients (f : group (q:=q) c hsk A w hA) (a : Index w q) : ℝ :=
  PolynomialArrayInterpolation.coefficients (fun u=>canonicalLog c (f.val u) a.1) a.2.val

lemma fullCoeff_coefficients (f : group (q:=q) c hsk A w hA) (i : Fin n) :
    fullCoeff w (coefficients c hsk A w hA f) i=
      PolynomialArrayInterpolation.coefficients (fun u=>canonicalLog c (f.val u) i) := by
  funext e
  dsimp only [fullCoeff]
  split_ifs with he
  · rfl
  · exact (coefficients_zero_high (f.property i) le_rfl e (Nat.lt_of_not_ge he)).symm

lemma toLog_coefficients (f : group (q:=q) c hsk A w hA) (u : Fin q → ℝ) :
    toLog w (coefficients c hsk A w hA f) u=canonicalLog c (f.val u) := by
  funext i
  rw [toLog,fullCoeff_coefficients]
  exact reconstruction_function (f.property i) u

lemma coefficients_toLog (x : Index w q → ℝ) (a : Index w q) :
    PolynomialArrayInterpolation.coefficients (fun u=>toLog w x u a.1) a.2.val=x a := by
  rw [show (fun u=>toLog w x u a.1)=gridEval (fullCoeff w x a.1) from rfl,
    coefficients_gridEval]
  simp only [fullCoeff,dite_eq_left a.2.property]

lemma toLog_continuous (u : Fin q → ℝ) : Continuous (fun x : Index w q → ℝ=>toLog w x u) := by
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro e he
  apply Continuous.mul _ continuous_const
  unfold fullCoeff
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma coefficients_continuous : Continuous (coefficients (q:=q) c hsk A w hA) := by
  apply continuous_pi
  intro a
  apply (PolynomialArrayInterpolation.coefficients_continuous a.2.val).comp
  apply continuous_pi
  intro u
  exact (continuous_apply a.1).comp ((canonicalLog_continuous c).comp
    ((continuous_apply u).comp continuous_subtype_val))

def coefficientHomeomorph : group (q:=q) c hsk A w hA ≃ₜ (Index w q → ℝ) where
  toFun:=coefficients c hsk A w hA
  invFun x:=⟨fun u=>canonicalExp c (toLog w x u),toLog_array c w x⟩
  left_inv f:=by
    apply Subtype.ext
    funext u
    change canonicalExp c (toLog w (coefficients c hsk A w hA f) u)=f.val u
    rw [toLog_coefficients,canonicalExp_log]
  right_inv x:=by
    funext a
    change PolynomialArrayInterpolation.coefficients
      (fun u=>canonicalLog c (canonicalExp c (toLog w x u)) a.1) a.2.val=x a
    simp only [canonicalLog_exp]
    exact coefficients_toLog w x a
  continuous_toFun:=coefficients_continuous c hsk A w hA
  continuous_invFun:=by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro u
    exact (logHomeomorph c).symm.continuous.comp (toLog_continuous w u)

lemma coefficientHomeomorph_one : coefficientHomeomorph (q:=q) c hsk A w hA 1=0 := by
  funext a
  change PolynomialArrayInterpolation.coefficients (fun u=>canonicalLog c (1:G) a.1) a.2.val=0
  simp [PolynomialArrayInterpolation.coefficients,canonicalLog_one]

end RationalLattice.PolynomialArrays

end
end
end

end OAI
