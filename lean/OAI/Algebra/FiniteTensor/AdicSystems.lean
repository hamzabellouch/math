import Mathlib

namespace OAI

/-! Quadratic remainders, adic contraction and Tougeron corrections. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

def mvShift (a : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (fun i=>C (a i)+X i)

def mvLinearPart (a : σ → R) (f : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ i : σ,C (eval a (pderiv i f))*X i

def mvRemainder (a : σ → R) (f : MvPolynomial σ R) : MvPolynomial σ R :=
  mvShift a f-C (eval a f)-mvLinearPart a f

private theorem mvLinearPart_mul_X (a : σ → R) (f : MvPolynomial σ R) (k : σ) :
    mvLinearPart a (f*X k)=mvLinearPart a f*C (a k)+C (eval a f)*X k := by
  simp only [mvLinearPart,pderiv_mul,map_add,map_mul,eval_X,add_mul,
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · rw [Finset.sum_eq_single k]
    · simp
    · intro i hi hik
      simp [pderiv_X,Ne.symm hik]
    · simp

private theorem mvRemainder_mul_X (a : σ → R) (f : MvPolynomial σ R) (k : σ) :
    mvRemainder a (f*X k)=mvRemainder a f*(C (a k)+X k)+mvLinearPart a f*X k := by
  rw [mvRemainder,mvRemainder,mvLinearPart_mul_X]
  simp only [map_mul,eval_X,mvShift,aeval_X]
  ring

private theorem mvRemainder_mem (a : σ → R) (f : MvPolynomial σ R) :
    mvRemainder a f ∈ Ideal.span (Set.range (fun ij : σ×σ=>(X ij.1*X ij.2 : MvPolynomial σ R))) := by
  let J : Ideal (MvPolynomial σ R) := Ideal.span (Set.range (fun ij : σ×σ=>X ij.1*X ij.2))
  change mvRemainder a f∈J
  induction f using MvPolynomial.induction_on with
  | C r =>
    have h : mvRemainder a (C r)=0 := by
      simp only [mvRemainder,mvShift,aeval_C,eval_C,mvLinearPart,pderiv_C,
        map_zero,zero_mul,Finset.sum_const_zero,sub_zero]
      change C r-C r=0
      exact sub_self _
    rw [h]
    exact J.zero_mem
  | add f g hf hg =>
    have h : mvRemainder a (f+g)=mvRemainder a f+mvRemainder a g := by
      simp only [mvRemainder,map_add,mvLinearPart,map_add,add_mul,Finset.sum_add_distrib]
      ring
    rw [h]
    exact J.add_mem hf hg
  | mul_X f k hf =>
    rw [mvRemainder_mul_X]
    apply J.add_mem (J.mul_mem_right _ hf)
    rw [mvLinearPart,Finset.sum_mul]
    apply J.sum_mem
    intro i hi
    have h : X i*X k∈J := Ideal.subset_span (Set.mem_range_self (i,k))
    simpa only [mul_assoc] using J.mul_mem_left (C (eval a (pderiv i f))) h

 
theorem mv_polynomial_quadratic_remainder (f : MvPolynomial σ R) (a : σ → R) :
    ∃ q : σ → σ → MvPolynomial σ R,
      mvShift a f=C (eval a f)+mvLinearPart a f+
        ∑ i : σ,∑ j : σ,X i*X j*q i j := by
  obtain ⟨q,hq⟩ := Ideal.mem_span_range_iff_exists_fun.mp (mvRemainder_mem a f)
  refine ⟨fun i j=>q (i,j),?_⟩
  have he : (∑ i : σ,∑ j : σ,X i*X j*q (i,j))=mvRemainder a f := by
    rw [←Finset.sum_product']
    rw [Finset.univ_product_univ]
    calc
      _ = ∑ ij : σ×σ,q ij*(X ij.1*X ij.2) := by
        apply Finset.sum_congr rfl
        intro ij hij
        cases ij
        exact mul_comm _ _
      _ = _ := hq
  rw [he,mvRemainder]
  ring

 

theorem mv_eval_quadratic_remainder (f : MvPolynomial σ R) (a : σ → R) :
    ∃ q : σ → σ → MvPolynomial σ R,∀ h : σ → R,
      eval (a+h) f=eval a f+(∑ i : σ,eval a (pderiv i f)*h i)+
        ∑ i : σ,∑ j : σ,h i*h j*eval h (q i j) := by
  obtain ⟨q,hq⟩ := mv_polynomial_quadratic_remainder f a
  refine ⟨q,?_⟩
  intro h
  have he := congrArg (eval h) hq
  have hshift : eval h (mvShift a f)=eval (a+h) f := by
    have hh : (eval h).comp (mvShift a).toRingHom=eval (a+h) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply,mvShift,AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom,aeval_C,algebraMap_eq,eval_C]
      · intro i
        change eval h ((aeval (fun i=>C (a i)+X i)) (X i)) = _
        simp only [aeval_X,map_add,eval_C,eval_X,Pi.add_apply]
    exact RingHom.congr_fun hh f
  simpa only [hshift,map_add,map_sum,map_mul,eval_C,eval_X,mvLinearPart]
    using he

end
end PD4Tensor.Spreading

 

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

 
omit [Fintype σ] [DecidableEq σ] in
theorem mv_eval_sub_mem (J : Ideal R) (f : MvPolynomial σ R) (u v : σ → R)
    (h : ∀ i,u i-v i∈J) : eval u f-eval v f∈J := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub,sub_eq_zero]
  have he : (Ideal.Quotient.mk J).comp (eval u)=(Ideal.Quotient.mk J).comp (eval v) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp only [RingHom.comp_apply,eval_X]
      exact sub_eq_zero.mp ((map_sub _ _ _).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr (h i)))
  exact RingHom.congr_fun he f

 
omit [DecidableEq σ] in
theorem mv_quadratic_sub_mem (I : Ideal R) (n : ℕ)
    (q : σ → σ → MvPolynomial σ R) (u v : σ → R)
    (hu : ∀i,u i∈I) (hv : ∀i,v i∈I) (h : ∀i,u i-v i∈I^n) :
    (∑ i : σ,∑ j : σ,u i*u j*eval u (q i j))-
      (∑ i : σ,∑ j : σ,v i*v j*eval v (q i j))∈I^(n+1) := by
  rw [←Finset.sum_sub_distrib]
  apply Ideal.sum_mem
  intro i hi
  rw [←Finset.sum_sub_distrib]
  apply Ideal.sum_mem
  intro j hj
  have he : u i*u j*eval u (q i j)-v i*v j*eval v (q i j)=
      (u i-v i)*u j*eval u (q i j)+
      v i*(u j-v j)*eval u (q i j)+
      v i*v j*(eval u (q i j)-eval v (q i j)) := by ring
  rw [he]
  apply Ideal.add_mem
  · apply Ideal.add_mem
    · apply Ideal.mul_mem_right
      rw [pow_succ]
      exact Ideal.mul_mem_mul (h i) (hu j)
    · apply Ideal.mul_mem_right
      rw [pow_succ']
      exact Ideal.mul_mem_mul (hv i) (h j)
  · rw [mul_assoc]
    apply Ideal.mul_mem_left
    rw [pow_succ']
    exact Ideal.mul_mem_mul (hv j) (mv_eval_sub_mem _ _ _ _ h)

 

omit [DecidableEq σ] in
theorem adic_quadratic_system (I : Ideal R) [IsAdicComplete I R]
    (e : σ → R) (he : ∀i,e i∈I) (q : σ → σ → σ → MvPolynomial σ R) :
    ∃ z : σ → R,(∀i,z i∈I) ∧ ∀k,
      e k+z k+∑ i : σ,∑ j : σ,z i*z j*eval z (q k i j)=0 := by
  let Q (z : σ → R) (k : σ) : R := ∑ i : σ,∑ j : σ,z i*z j*eval z (q k i j)
  let c : ℕ → σ → R := fun n=>Nat.recOn n 0 (fun _ z k=>-e k-Q z k)
  have hc (n : ℕ) (k : σ) : c (n+1) k=-e k-Q (c n) k := rfl
  have hmem : ∀ n k,c n k∈I := by
    intro n
    induction n with
    | zero => intro k; exact I.zero_mem
    | succ n ih =>
      intro k
      rw [hc]
      apply I.sub_mem (I.neg_mem (he k))
      apply I.sum_mem
      intro i hi
      apply I.sum_mem
      intro j hj
      exact I.mul_mem_right _ (I.mul_mem_right _ (ih i))
  have hstep : ∀ n k,c (n+1) k-c n k∈I^(n+1) := by
    intro n
    induction n with
    | zero =>
      intro k
      simpa only [Nat.zero_add,pow_one,show c 0 k=0 from rfl,sub_zero] using hmem 1 k
    | succ n ih =>
      intro k
      rw [hc (n+1),hc n]
      have hh := mv_quadratic_sub_mem I (n+1) (q k) (c (n+1)) (c n)
        (hmem (n+1)) (hmem n) ih
      have heq : -e k-Q (c (n+1)) k-(-e k-Q (c n) k)=
          -(Q (c (n+1)) k-Q (c n) k) := by ring
      rw [heq]
      exact (I^((n+1)+1)).neg_mem hh
  have hdiff : ∀ m n,m ≤ n → ∀k,c m k-c n k∈I^m := by
    intro m n hmn
    obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hmn
    induction l with
    | zero => intro k; simp only [add_zero,sub_self]; exact Ideal.zero_mem _
    | succ l ih =>
      intro k
      have ha := Ideal.pow_le_pow_right (by omega : m ≤ m+l+1) (hstep (m+l) k)
      have hb := (I^m).sub_mem (ih (by omega) k) ha
      convert hb using 1
      simp only [Nat.add_assoc]
      ring
  have hex : ∀k,∃z : R,∀n,c n k-z∈I^n := by
    intro k
    obtain ⟨z,hz⟩ := IsPrecomplete.prec' (I:=I) (fun n=>c n k) (by
      intro m n hmn
      rw [←Ideal.one_eq_top,Ideal.smul_eq_mul,mul_one]
      exact SModEq.sub_mem.mpr (hdiff m n hmn k))
    refine ⟨z,?_⟩
    intro n
    specialize hz n
    rw [←Ideal.one_eq_top,Ideal.smul_eq_mul,mul_one] at hz
    exact SModEq.sub_mem.mp hz
  choose z hz using hex
  have hzi (k : σ) : z k∈I := by
    have hh := hz k 1
    rw [pow_one] at hh
    have h := I.sub_mem (hmem 1 k) hh
    simpa only [sub_sub_cancel] using h
  refine ⟨z,hzi,?_⟩
  intro k
  apply IsHausdorff.haus' (I:=I)
  intro n
  rw [←Ideal.one_eq_top,Ideal.smul_eq_mul,mul_one,SModEq.zero]
  have hq := mv_quadratic_sub_mem I n (q k) (c n) z (hmem n) hzi (fun i=>hz i n)
  have hqn : Q (c n) k-Q z k∈I^n :=
    Ideal.pow_le_pow_right (by omega : n ≤ n+1) hq
  have hcn : c (n+1) k-z k∈I^n :=
    Ideal.pow_le_pow_right (by omega : n ≤ n+1) (hz k (n+1))
  have hh := (I^n).neg_mem ((I^n).add_mem hcn hqn)
  rw [hc] at hh
  convert hh using 1
  dsimp only [Q]
  ring

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

 

omit [Fintype σ] [DecidableEq σ] in
theorem adic_contractive_system (I : Ideal R) [IsAdicComplete I R]
    (e : σ → R) (he : ∀ i,e i∈I) (Q : (σ → R) → σ → R)
    (hQI : ∀ z,(∀ i,z i∈I) → ∀ k,Q z k∈I)
    (hQC : ∀ n u v,(∀ i,u i∈I) → (∀ i,v i∈I) →
      (∀ i,u i-v i∈I^n) → ∀ k,Q u k-Q v k∈I^(n+1)) :
    ∃ z : σ → R,(∀ i,z i∈I) ∧ ∀ k,e k+z k+Q z k=0 := by
  let c : ℕ → σ → R := fun n=>Nat.recOn n 0 (fun _ z k=>-e k-Q z k)
  have hc (n : ℕ) (k : σ) : c (n+1) k=-e k-Q (c n) k := rfl
  have hmem : ∀ n k,c n k∈I := by
    intro n
    induction n with
    | zero => intro k; exact I.zero_mem
    | succ n ih =>
      intro k
      rw [hc]
      apply I.sub_mem (I.neg_mem (he k))
      exact hQI (c n) ih k
  have hstep : ∀ n k,c (n+1) k-c n k∈I^(n+1) := by
    intro n
    induction n with
    | zero =>
      intro k
      simpa only [Nat.zero_add,pow_one,show c 0 k=0 from rfl,sub_zero] using hmem 1 k
    | succ n ih =>
      intro k
      rw [hc (n+1),hc n]
      have hh := hQC (n+1) (c (n+1)) (c n) (hmem (n+1)) (hmem n) ih k
      have heq : -e k-Q (c (n+1)) k-(-e k-Q (c n) k)=
          -(Q (c (n+1)) k-Q (c n) k) := by ring
      rw [heq]
      exact (I^((n+1)+1)).neg_mem hh
  have hdiff : ∀ m n,m ≤ n → ∀k,c m k-c n k∈I^m := by
    intro m n hmn
    obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hmn
    induction l with
    | zero => intro k; simp only [add_zero,sub_self]; exact Ideal.zero_mem _
    | succ l ih =>
      intro k
      have ha := Ideal.pow_le_pow_right (by omega : m ≤ m+l+1) (hstep (m+l) k)
      have hb := (I^m).sub_mem (ih (by omega) k) ha
      convert hb using 1
      simp only [Nat.add_assoc]
      ring
  have hex : ∀k,∃z : R,∀n,c n k-z∈I^n := by
    intro k
    obtain ⟨z,hz⟩ := IsPrecomplete.prec' (I:=I) (fun n=>c n k) (by
      intro m n hmn
      rw [←Ideal.one_eq_top,Ideal.smul_eq_mul,mul_one]
      exact SModEq.sub_mem.mpr (hdiff m n hmn k))
    refine ⟨z,?_⟩
    intro n
    specialize hz n
    rw [←Ideal.one_eq_top,Ideal.smul_eq_mul,mul_one] at hz
    exact SModEq.sub_mem.mp hz
  choose z hz using hex
  have hzi (k : σ) : z k∈I := by
    have hh := hz k 1
    rw [pow_one] at hh
    have h := I.sub_mem (hmem 1 k) hh
    simpa only [sub_sub_cancel] using h
  refine ⟨z,hzi,?_⟩
  intro k
  apply IsHausdorff.haus' (I:=I)
  intro n
  rw [←Ideal.one_eq_top,Ideal.smul_eq_mul,mul_one,SModEq.zero]
  have hq := hQC n (c n) z (hmem n) hzi (fun i=>hz i n) k
  have hqn : Q (c n) k-Q z k∈I^n :=
    Ideal.pow_le_pow_right (by omega : n ≤ n+1) hq
  have hcn : c (n+1) k-z k∈I^n :=
    Ideal.pow_le_pow_right (by omega : n ≤ n+1) (hz k (n+1))
  have hh := (I^n).neg_mem ((I^n).add_mem hcn hqn)
  rw [hc] at hh
  convert hh using 1
  ring

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
theorem mv_quadratic_mixed_sub_mem (I : Ideal R) (n : ℕ)
    (q : σ → σ → MvPolynomial σ R) (u v u' v' : σ → R)
    (hu : ∀i,u i∈I) (hv : ∀i,v i∈I) (h : ∀i,u i-v i∈I^n) (h' : ∀i,u' i-v' i∈I^n) :
    (∑ i : σ,∑ j : σ,u i*u j*eval u' (q i j))-
      (∑ i : σ,∑ j : σ,v i*v j*eval v' (q i j))∈I^(n+1) := by
  rw [←Finset.sum_sub_distrib]
  apply Ideal.sum_mem
  intro i hi
  rw [←Finset.sum_sub_distrib]
  apply Ideal.sum_mem
  intro j hj
  have he : u i*u j*eval u' (q i j)-v i*v j*eval v' (q i j)=
      (u i-v i)*u j*eval u' (q i j)+
      v i*(u j-v j)*eval u' (q i j)+
      v i*v j*(eval u' (q i j)-eval v' (q i j)) := by ring
  rw [he]
  apply Ideal.add_mem
  · apply Ideal.add_mem
    · apply Ideal.mul_mem_right
      rw [pow_succ]
      exact Ideal.mul_mem_mul (h i) (hu j)
    · apply Ideal.mul_mem_right
      rw [pow_succ']
      exact Ideal.mul_mem_mul (hv i) (h j)
  · rw [mul_assoc]
    apply Ideal.mul_mem_left
    rw [pow_succ']
    exact Ideal.mul_mem_mul (hv j) (mv_eval_sub_mem _ _ _ _ h')

omit [DecidableEq σ] in
private theorem mulVec_mem_ideal (I : Ideal R) (A : Matrix σ σ R) (z : σ → R)
    (hz : ∀ i,z i∈I) (k : σ) : (A*ᵥz) k∈I := by
  apply I.sum_mem
  intro i hi
  exact I.mul_mem_left _ (hz i)

omit [DecidableEq σ] in
private theorem mulVec_sub_mem_ideal (I : Ideal R) (A : Matrix σ σ R) (u v : σ → R)
    (h : ∀ i,u i-v i∈I) (k : σ) : (A*ᵥu) k-(A*ᵥv) k∈I := by
  rw [←Pi.sub_apply,←Matrix.mulVec_sub]
  exact mulVec_mem_ideal I A (u-v) h k

 

theorem mv_tougeron_correction (I : Ideal R) [IsAdicComplete I R]
    (f : σ → MvPolynomial σ R) (a e : σ → R)
    (he : ∀ k,e k∈I)
    (hf : ∀ k,eval a (f k)=
      (Matrix.det (fun k i=>eval a (pderiv i (f k))))^2*e k) :
    ∃ b : σ → R,(∀ k,eval b (f k)=0) ∧ ∀ i,∃ v∈I,
      b i=a i+(Matrix.det (fun k i=>eval a (pderiv i (f k))))*v := by
  let J : Matrix σ σ R := fun k i=>eval a (pderiv i (f k))
  let δ : R := J.det
  let A : Matrix σ σ R := J.adjugate
  choose q hq using fun k=>mv_eval_quadratic_remainder (f k) a
  let Q (z : σ → R) (k : σ) : R :=
    ∑ i : σ,∑ j : σ,(A*ᵥz) i*(A*ᵥz) j*eval (δ • (A*ᵥz)) (q k i j)
  have hQI (z : σ → R) (hz : ∀ i,z i∈I) (k : σ) : Q z k∈I := by
    apply I.sum_mem
    intro i hi
    apply I.sum_mem
    intro j hj
    exact I.mul_mem_right _ (I.mul_mem_right _ (mulVec_mem_ideal I A z hz i))
  have hQC (n : ℕ) (u v : σ → R) (hu : ∀ i,u i∈I) (hv : ∀ i,v i∈I)
      (huv : ∀ i,u i-v i∈I^n) (k : σ) : Q u k-Q v k∈I^(n+1) := by
    apply mv_quadratic_mixed_sub_mem I n (q k) (A*ᵥu) (A*ᵥv)
      (δ • (A*ᵥu)) (δ • (A*ᵥv))
      (mulVec_mem_ideal I A u hu) (mulVec_mem_ideal I A v hv)
      (mulVec_sub_mem_ideal (I^n) A u v huv)
    intro i
    simpa only [Pi.smul_apply,smul_eq_mul,mul_sub] using
      (I^n).mul_mem_left δ (mulVec_sub_mem_ideal (I^n) A u v huv i)
  obtain ⟨z,hz,hroot⟩ := adic_contractive_system I e he Q hQI hQC
  let h : σ → R := δ • (A*ᵥz)
  have hlin : J*ᵥh=δ^2 • z := by
    dsimp only [h,A]
    rw [Matrix.mulVec_smul,Matrix.mulVec_mulVec,Matrix.mul_adjugate,
      Matrix.smul_mulVec,Matrix.one_mulVec,smul_smul]
    simp only [δ,pow_two]
  refine ⟨a+h,?_,?_⟩
  · intro k
    rw [hq k h,hf k]
    have hl : (∑ i : σ,eval a (pderiv i (f k))*h i)=δ^2*z k := by
      exact congrFun hlin k
    rw [hl]
    have hquad : (∑ i : σ,∑ j : σ,h i*h j*eval h (q k i j))=δ^2*Q z k := by
      dsimp only [Q,h]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Pi.smul_apply,smul_eq_mul]
      ring
    rw [hquad]
    change δ^2*e k+δ^2*z k+δ^2*Q z k=0
    rw [←mul_add,←mul_add,hroot k,mul_zero]
  · intro i
    refine ⟨(A*ᵥz) i,mulVec_mem_ideal I A z hz i,?_⟩
    rfl

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

private theorem det_sub_mem_ideal (I : Ideal R) (A B : Matrix σ σ R)
    (h : ∀ i j,A i j-B i j∈I) : A.det-B.det∈I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub,sub_eq_zero,RingHom.map_det,RingHom.map_det]
  congr 1
  ext i j
  change Ideal.Quotient.mk I (A i j)=Ideal.Quotient.mk I (B i j)
  exact sub_eq_zero.mp ((map_sub _ _ _).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr (h i j)))

 

theorem corrected_jacobian_factor (I : Ideal R) (f : σ → MvPolynomial σ R)
    (a b : σ → R)
    (hab : ∀ i,∃ v∈I,b i=a i+(Matrix.det (fun k j=>eval a (pderiv j (f k))))*v) :
    ∃ r∈I,Matrix.det (fun k j=>eval b (pderiv j (f k)))=
      (Matrix.det (fun k j=>eval a (pderiv j (f k))))*(1+r) := by
  let δ := Matrix.det (fun k j=>eval a (pderiv j (f k)))
  have hc (i : σ) : b i-a i∈Ideal.span {δ}*I := by
    obtain ⟨v,hv,h⟩ := hab i
    apply Ideal.mem_span_singleton_mul.mpr
    exact ⟨v,hv,by rw [h]; ring⟩
  have hdet := det_sub_mem_ideal (Ideal.span {δ}*I)
    (fun k j=>eval b (pderiv j (f k))) (fun k j=>eval a (pderiv j (f k)))
    (fun k j=>mv_eval_sub_mem _ _ _ _ hc)
  obtain ⟨r,hr,heq⟩ := Ideal.mem_span_singleton_mul.mp hdet
  refine ⟨r,hr,?_⟩
  change _=δ*(1+r)
  change δ*r=Matrix.det (fun k j=>eval b (pderiv j (f k)))-δ at heq
  linear_combination -heq

 

theorem mv_tougeron_nondegenerate [IsDomain R] (I : Ideal R) [IsAdicComplete I R]
    (f : σ → MvPolynomial σ R) (a e : σ → R)
    (he : ∀ k,e k∈I)
    (hJ : Matrix.det (fun k i=>eval a (pderiv i (f k)))≠0)
    (hf : ∀ k,eval a (f k)=
      (Matrix.det (fun k i=>eval a (pderiv i (f k))))^2*e k) :
    ∃ b : σ → R,(∀ k,eval b (f k)=0) ∧
      (Matrix.det (fun k i=>eval b (pderiv i (f k)))≠0) ∧
      ∀ i,∃ v∈I,b i=a i+(Matrix.det (fun k j=>eval a (pderiv j (f k))))*v := by
  obtain ⟨b,hb,hclose⟩ := mv_tougeron_correction I f a e he hf
  obtain ⟨r,hr,hfactor⟩ := corrected_jacobian_factor I f a b hclose
  refine ⟨b,hb,?_,hclose⟩
  rw [hfactor]
  apply mul_ne_zero hJ
  have hu : IsUnit (1+r) := by
    simpa only [mul_one,add_comm] using
      (Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot I hr) 1)
  exact hu.ne_zero

end
end PD4Tensor.Spreading
end

end OAI
