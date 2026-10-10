import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Interaction

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def polynomialCoeffLinear (R : Type*) [CommRing R] [Algebra ℚ R] (s : ℕ) :
    Polynomial R →ₗ[ℚ] R where
  toFun p := p.coeff s
  map_add' p q := Polynomial.coeff_add p q s
  map_smul' r p := by simp

noncomputable def relativeCoeffB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) (s : ℕ) :
    B a μ d ⊗[ℚ] B a μ e →ₗ[ℚ] B a μ d ⊗[ℚ] B a μ e :=
  (polynomialCoeffLinear (B a μ d ⊗[ℚ] B a μ e) s).comp
    (relativeTaylorB a μ d e).toLinearMap

@[simp] lemma relativeCoeffB_tmul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (s : ℕ) (f : B a μ d) (g : B a μ e) :
    relativeCoeffB a μ d e s (f ⊗ₜ[ℚ] g)=(taylorB a μ d f).coeff s ⊗ₜ[ℚ] g := by
  change (relativeTaylorB a μ d e (f ⊗ₜ[ℚ] g)).coeff s=_
  rw [relativeTaylorB_tmul,Polynomial.coeff_mul_C,Polynomial.coeff_map]
  change ((taylorB a μ d f).coeff s ⊗ₜ[ℚ] 1) * (1 ⊗ₜ[ℚ] g)=_
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

theorem relativeCoeffB_graded (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : B a μ d ⊗[ℚ] B a μ e) (k : ℤ)
    (hx : ∀ m n,m+n≠k → TensorProduct.map (componentB a μ d m) (componentB a μ e n) x=0)
    (s : ℕ) (p q : ℤ) (h : p+q≠k-s) :
    TensorProduct.map (componentB a μ d p) (componentB a μ e q) (relativeCoeffB a μ d e s x)=0 := by
  classical
  let F := (TensorProduct.map (componentB a μ d p) (componentB a μ e q)).comp (relativeCoeffB a μ d e s)
  change F x=0
  obtain ⟨t,ht,he⟩ := SplitTree.componentTensor_finite_decomposition a μ (.node (.leaf d) (.leaf e)) x
  change (∑ mn∈t,TensorProduct.map (componentB a μ d mn.1) (componentB a μ e mn.2) x)=x at he
  have hterm : ∀ mn∈t,F (TensorProduct.map (componentB a μ d mn.1) (componentB a μ e mn.2) x)=0 := by
    intro mn hmn
    by_cases hm : mn.1+mn.2=k
    · have hsep : p≠mn.1-s ∨ q≠mn.2 := by
        by_contra hh
        push Not at hh
        apply h
        rw [hh.1,hh.2,← hm]
        ring
      generalize x=y
      induction y using TensorProduct.inductionOn with
      | tmul f g =>
        change TensorProduct.map (componentB a μ d p) (componentB a μ e q)
          (relativeCoeffB a μ d e s (componentB a μ d mn.1 f ⊗ₜ[ℚ] componentB a μ e mn.2 g))=0
        rw [relativeCoeffB_tmul,TensorProduct.map_tmul,
          componentB_on_grade a μ d p (mn.1-s) _
            (taylorB_coeff_graded a μ d _ mn.1 ⟨f,rfl⟩ s),
          componentB_on_grade a μ e q mn.2 _ ⟨g,rfl⟩]
        rcases hsep with hp|hq
        · rw [ite_eq_right hp,TensorProduct.zero_tmul]
        · rw [ite_eq_right hq,TensorProduct.tmul_zero]
      | add y z hy hz => simp only [map_add,hy,hz,add_zero]
    · rw [hx mn.1 mn.2 hm,map_zero]
  calc
    F x=F (∑ mn∈t,TensorProduct.map (componentB a μ d mn.1) (componentB a μ e mn.2) x) := congrArg F he.symm
    _=0 := by rw [map_sum]; exact Finset.sum_eq_zero hterm

theorem relative_restriction_graded (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (A : Cut d e) (f : B a (SlopeArithmetic.slope c η) (d+e))
    (k : ℤ) (hf : f∈gradeB a (SlopeArithmetic.slope c η) (d+e) k)
    (s : ℕ) (p q : ℤ) (h : p+q≠k-s) :
    TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d p)
      (componentB a (SlopeArithmetic.slope c η) e q)
      (relativeCoeffB a (SlopeArithmetic.slope c η) d e s (restrictionB a c η hc hs A f))=0 := by
  exact relativeCoeffB_graded a _ d e _ k (fun m n hm=>restrictionB_graded a c η hc hs A f k hf m n hm) s p q h

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def polynomialMapLinear {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (l : R →ₗ[ℚ] S) : Polynomial R →ₗ[ℚ] Polynomial S where
  toFun p := Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange l l.map_zero))
  map_add' p q := by
    ext s
    exact l.map_add (p.coeff s) (q.coeff s)
  map_smul' r p := by
    ext s
    exact l.map_smul r (p.coeff s)

@[simp] lemma polynomialMapLinear_coeff {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (l : R →ₗ[ℚ] S) (p : Polynomial R) (n : ℕ) :
    (polynomialMapLinear l p).coeff n=l (p.coeff n) := rfl

omit [DecidableEq I] in
lemma eulerForm_add_left (a : I → I → ℕ) (d e f : I → ℕ) :
    eulerForm a (d+e) f=eulerForm a d f+eulerForm a e f := by
  simp only [eulerForm,Pi.add_apply,Nat.cast_add,add_mul,mul_add,Finset.sum_add_distrib]
  ring

omit [DecidableEq I] in
lemma eulerForm_add_right (a : I → I → ℕ) (d e f : I → ℕ) :
    eulerForm a d (e+f)=eulerForm a d e+eulerForm a d f := by
  simp only [eulerForm,Pi.add_apply,Nat.cast_add,mul_add,Finset.sum_add_distrib]
  ring

lemma coeff_single_toMvPolynomial {R α : Type*} [CommRing R] (i : α)
    (p : Polynomial R) (n : ℕ) :
    (Polynomial.toMvPolynomial i p).coeff (Finsupp.single i n)=p.coeff n := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,Polynomial.coeff_add,hp,hq]
  | monomial m r =>
    simp [← Polynomial.C_mul_X_pow_eq_monomial,MvPolynomial.coeff_X_pow,(Finsupp.single_injective i).eq_iff,eq_comm]

lemma restrictionTest_leaf_coeff (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (hs : (SplitTree.leaf d).OnSlope c η θ)
    (k : ℤ) (r : ℕ) (f : B a (SlopeArithmetic.slope c η) d) :
    restrictionTest a c η hc θ (.leaf d) hs rfl k (Finsupp.single () r) f =
      componentB a (SlopeArithmetic.slope c η) d k
        ((taylorB a (SlopeArithmetic.slope c η) d f).coeff r) := by
  change componentB a (SlopeArithmetic.slope c η) d k
    ((Polynomial.toMvPolynomial () (taylorB a (SlopeArithmetic.slope c η) d f)).coeff
      (Finsupp.single () r)) = _
  rw [coeff_single_toMvPolynomial]

noncomputable def relativeLeading (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (p q : ℤ) : B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      Polynomial (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e) :=
  (polynomialMapLinear (TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d p)
    (componentB a (SlopeArithmetic.slope c η) e q))).comp
      ((relativeTaylorB a (SlopeArithmetic.slope c η) d e).toLinearMap.comp
        (restrictionB a c η hc hs (firstCut d e)).toLinearMap)

theorem relativeLeading_divisible (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hd : d≠0) (_he : e≠0)
    (hdθ : SlopeArithmetic.slope c η d=θ) (heθ : SlopeArithmetic.slope c η e=θ)
    (hsym : eulerForm a d e=eulerForm a e d) (p q W : ℤ)
    (hw : 2*(p+q)+eulerForm a d d+eulerForm a e e=W)
    (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    Polynomial.X ^ (-eulerForm a d e).toNat ∣
      relativeLeading a c η hc (hdθ.trans heθ.symm) p q f := by
  classical
  apply Polynomial.X_pow_dvd_iff.mpr
  intro s hs
  let μ:=SlopeArithmetic.slope c η
  let F := (polynomialCoeffLinear
    (B a μ d ⊗[ℚ] B a μ e) s).comp
    (relativeLeading a c η hc (d:=d) (e:=e) (hdθ.trans heθ.symm) p q)
  change F f=0
  obtain ⟨t,ht,heq⟩ := componentB_finite_decomposition a μ (d+e) f
  have hterm : ∀ k∈t,F (componentB a μ (d+e) k f)=0 := by
    intro k hk
    by_cases hkdeg : p+q=k-s
    · have hsmall : 2*k+eulerForm a (d+e) (d+e)<W := by
        rw [eulerForm_add_left,eulerForm_add_right,eulerForm_add_right,← hsym]
        omega
      have slopeTot : SlopeArithmetic.slope c η (d+e)=θ :=
        (SlopeArithmetic.slope_add_same c η hc (hdθ.trans heθ.symm)).trans hdθ
      have hzero := hf (.leaf (d+e)) trivial
        ⟨SlopeArithmetic.add_ne_zero_left d e hd,slopeTot⟩ rfl k 0 hsmall
      rw [restrictionTest_leaf_zero] at hzero
      have hz : componentB a μ (d+e) k f = (0 : B a μ (d+e)) := hzero
      exact (congrArg F hz).trans F.map_zero
    · exact relative_restriction_graded a c η hc (hdθ.trans heθ.symm) (firstCut d e)
        (componentB a μ (d+e) k f) k ⟨f,rfl⟩ s p q hkdeg
  calc
    F f=F (∑ k∈t,componentB a μ (d+e) k f) := congrArg F heq.symm
    _=0 := by rw [map_sum]; exact Finset.sum_eq_zero hterm

theorem relativeLeading_taylor_divisible (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hd : d≠0) (_he : e≠0)
    (hdθ : SlopeArithmetic.slope c η d=θ) (heθ : SlopeArithmetic.slope c η e=θ)
    (r : ℕ) (hsym : eulerForm a d e=eulerForm a e d) (p q W : ℤ)
    (hw : 2*(p+q)+eulerForm a d d+eulerForm a e e=W)
    (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    Polynomial.X ^ (-eulerForm a d e).toNat ∣
      relativeLeading a c η hc (hdθ.trans heθ.symm) p q ((taylorB a (SlopeArithmetic.slope c η) (d+e) f).coeff r) := by
  classical
  apply Polynomial.X_pow_dvd_iff.mpr
  intro s hs
  let μ:=SlopeArithmetic.slope c η
  let F := (polynomialCoeffLinear
    (B a μ d ⊗[ℚ] B a μ e) s).comp
    (relativeLeading a c η hc (d:=d) (e:=e) (hdθ.trans heθ.symm) p q)
  let g := (taylorB a μ (d+e) f).coeff r
  change F g=0
  obtain ⟨t,ht,heq⟩ := componentB_finite_decomposition a μ (d+e) g
  have hterm : ∀ k∈t,F (componentB a μ (d+e) k g)=0 := by
    intro k hk
    by_cases hkdeg : p+q=k-s
    · have hsmall : 2*k+eulerForm a (d+e) (d+e)<W := by
        rw [eulerForm_add_left,eulerForm_add_right,eulerForm_add_right,← hsym]
        omega
      have slopeTot : SlopeArithmetic.slope c η (d+e)=θ :=
        (SlopeArithmetic.slope_add_same c η hc (hdθ.trans heθ.symm)).trans hdθ
      have hzero := hf (.leaf (d+e)) trivial
        ⟨SlopeArithmetic.add_ne_zero_left d e hd,slopeTot⟩ rfl k (Finsupp.single () r) hsmall
      rw [restrictionTest_leaf_coeff] at hzero
      have hz : componentB a μ (d+e) k g = (0 : B a μ (d+e)) := hzero
      exact (congrArg F hz).trans F.map_zero
    · exact relative_restriction_graded a c η hc (hdθ.trans heθ.symm) (firstCut d e)
        (componentB a μ (d+e) k g) k ⟨g,rfl⟩ s p q hkdeg
  calc
    F g=F (∑ k∈t,componentB a μ (d+e) k g) := congrArg F heq.symm
    _=0 := by rw [map_sum]; exact Finset.sum_eq_zero hterm

end ElementaryPositivity.RawShuffle

end

end OAI
