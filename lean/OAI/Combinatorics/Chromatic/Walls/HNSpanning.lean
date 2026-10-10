import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.Eval
import OAI.Combinatorics.Chromatic.Walls.HNGeometry

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable {A : Type*} [Ring A] [Algebra ℚ A]
variable (c η : I → ℝ) (V : (I → ℕ) → Submodule ℚ A)
noncomputable def hnWordSpace (l : List (I → ℕ)) : Submodule ℚ A := (l.map V).prod
omit [Fintype I] in
@[simp] lemma hnWordSpace_nil : hnWordSpace V []=1 := rfl
omit [Fintype I] in
@[simp] lemma hnWordSpace_cons (d : I → ℕ) (l : List (I → ℕ)) :
    hnWordSpace V (d::l)=V d*hnWordSpace V l := rfl
omit [Fintype I] in
@[simp] lemma hnWordSpace_singleton (d : I → ℕ) : hnWordSpace V [d]=V d := by simp
omit [Fintype I] in
lemma hnWordSpace_append (l r : List (I → ℕ)) :
    hnWordSpace V (l++r)=hnWordSpace V l*hnWordSpace V r := by simp [hnWordSpace,List.prod_append]

noncomputable def hnOrderedSpan (d : I → ℕ) : Submodule ℚ A :=
  ⨆ (l : List (I → ℕ)) (_ : l.sum=d) (_ : HNOrdered c η l),hnWordSpace V l
lemma hnWordSpace_le {d : I → ℕ} (l : List (I → ℕ)) (hs : l.sum=d) (ho : HNOrdered c η l) :
    hnWordSpace V l  ≤  hnOrderedSpan c η V d :=
  le_iSup_of_le l (le_iSup_of_le hs (le_iSup_of_le ho le_rfl))

variable (hc : ∀ i,0 < c i) (W : (I → ℕ) → Submodule ℚ A)
variable (hV : ∀ d,V d  ≤  W d)
variable (hW : ∀ d e,W d*W e  ≤  W (d+e))
variable (hzero : W 0  ≤  1)
variable (hdec : ∀ d,d≠0 → W d  ≤  V d ⊔
  ⨆ (u : I → ℕ) (v : I → ℕ) (_ : u+v=d) (_ : u≠0) (_ : v≠0)
    (_ : slope c η d < slope c η u),W u*W v)

include hc hV hW hzero hdec in

theorem hn_spanning (d : I → ℕ) : W d  ≤  hnOrderedSpan c η V d := by
  suffices ∀ n (d : I → ℕ),hnSize d=n → W d  ≤  hnOrderedSpan c η V d from this _ d rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro d hdn
    have small : ∀ e,hnSize e < hnSize d → W e  ≤  hnOrderedSpan c η V e :=
      fun e he=>ih _ (by omega) e rfl
    have words : ∀ s : HNComposition d,0 < polygonArea c η s.val →
        hnWordSpace V s.val  ≤  hnOrderedSpan c η V d := by
      intro s
      induction s using (hnBefore_wellFounded c η d).induction with
      | h s ihs =>
        intro ha
        by_cases ho : HNOrdered c η s.val
        · exact hnWordSpace_le c η V s.val s.property.1 ho
        obtain ⟨p,q,u,v,hs,huv⟩:=not_hnOrdered_adjacent c η s.property.2 ho
        have hn : ∀ b∈p++[u,v]++q,b≠0 := by simpa only [←hs] using s.property.2
        have hsum : (p++[u,v]++q).sum=d := hs ▸ s.property.1
        have hp : 0 < polygonArea c η (p++[u,v]++q) := hs ▸ ha
        have hdim : hnSize (u+v) < hnSize d :=
          (hnSize_pair_lt c η hc hn huv hp).trans_eq (congrArg hnSize hsum)
        have hmerge : V u*V v  ≤  hnOrderedSpan c η V (u+v) :=
          (mul_le_mul' (hV u) (hV v)).trans ((hW u v).trans (small (u+v) hdim))
        calc
          hnWordSpace V s.val = hnWordSpace V p*(V u*V v)*hnWordSpace V q := by
            rw [hs]; simp only [hnWordSpace_append,hnWordSpace_cons,hnWordSpace_nil,mul_one]
          _  ≤  hnWordSpace V p*hnOrderedSpan c η V (u+v)*hnWordSpace V q := by
            exact mul_le_mul' (mul_le_mul' le_rfl hmerge) le_rfl
          _  ≤  hnOrderedSpan c η V d := by
            unfold hnOrderedSpan
            simp only [Submodule.mul_iSup,Submodule.iSup_mul]
            refine iSup_le fun r=>iSup_le fun hr=>iSup_le fun hor=>?_
            let t : HNComposition d := ⟨p++r++q,by
              constructor
              · simpa only [List.sum_append,hr,List.sum_cons,List.sum_nil,add_zero] using hsum
              · intro b hb
                rcases List.mem_append.mp hb with hb|hb
                · rcases List.mem_append.mp hb with hb|hb
                  · exact hn b (by simp [hb])
                  · exact hor.1 b hb
                · exact hn b (by simp [hb])⟩
            have ht : HNBefore c η t s := by
              have := reorder_progress c η hc p q r (hn u (by simp)) (hn v (by simp)) huv hr hor
              simpa only [HNBefore,t,hs] using this
            have hat : 0 < polygonArea c η t.val := by
              rcases ht with ht|⟨ht,_⟩
              · exact lt_trans ha ht
              · exact ha.trans_eq ht
            have h := ihs t ht hat
            simpa only [t,hnWordSpace_append,hnOrderedSpan] using h
    by_cases hd : d=0
    · subst d
      exact hzero.trans (hnWordSpace_le c η V [] rfl ⟨by simp,by simp⟩)
    apply (hdec d hd).trans
    apply sup_le
    · simpa only [hnWordSpace_singleton] using (hnWordSpace_le c η V (d:=d) [d] (by simp) ⟨by simpa using hd,by simp⟩)
    refine iSup_le fun u=>iSup_le fun v=>iSup_le fun huv=>iSup_le fun hu=>
      iSup_le fun hv=>iSup_le fun hμ=>?_
    have hsize : hnSize u+hnSize v=hnSize d := by rw [←hnSize_add,huv]
    have hu₀ : hnSize u≠0 := (hnSize_eq_zero u).not.mpr hu
    have hv₀ : hnSize v≠0 := (hnSize_eq_zero v).not.mpr hv
    apply (mul_le_mul' (small u (by omega)) (small v (by omega))).trans
    unfold hnOrderedSpan
    simp only [Submodule.mul_iSup,Submodule.iSup_mul]
    refine iSup_le fun r=>iSup_le fun hr=>iSup_le fun hor=>
      iSup_le fun l=>iSup_le fun hl=>iSup_le fun hol=>?_
    let s : HNComposition d := ⟨l++r,by
      constructor
      · simpa only [List.sum_append,hl,hr] using huv
      · intro b hb
        rcases List.mem_append.mp hb with hb|hb
        · exact hol.1 b hb
        · exact hor.1 b hb⟩
    have hp : 0 < polygonArea c η s.val := by
      change 0 < polygonArea c η (l++r)
      rw [polygonArea_append,hl,hr]
      exact add_pos_of_nonneg_of_pos (add_nonneg (polygonArea_nonneg c η hc hol)
        (polygonArea_nonneg c η hc hor))
        (slopeCross_of_destabilizing c η hc hu (by simpa only [huv] using hμ))
    simpa only [s,hnWordSpace_append,hnOrderedSpan] using words s hp

end ElementaryPositivity.SlopeArithmetic

end
section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial

noncomputable def mapLinear {A B σ : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (l : A →ₗ[ℚ] B) :
    MvPolynomial σ A →ₗ[ℚ] MvPolynomial σ B where
  toFun p := AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).mapRange l l.map_zero)
  map_add' p q := by ext s; exact l.map_add (p.coeff s) (q.coeff s)
  map_smul' r p := by ext s; exact l.map_smul r (p.coeff s)

@[simp] lemma coeff_mapLinear {A B σ : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (l : A →ₗ[ℚ] B)
    (p : MvPolynomial σ A) (s : σ →₀ ℕ) :
    (mapLinear l p).coeff s = l (p.coeff s) := rfl

@[simp] lemma mapLinear_monomial {A B σ : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (l : A →ₗ[ℚ] B) (s : σ →₀ ℕ) (a : A) :
    mapLinear l (monomial s a) = monomial s (l a) := by
  classical
  ext t
  simp only [coeff_mapLinear,coeff_monomial]
  split_ifs <;> simp

noncomputable def evalRat {A σ : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → ℚ) : MvPolynomial σ A →ₐ[ℚ] A :=
  (aeval (fun i => algebraMap ℚ A (v i))).restrictScalars ℚ

@[simp] lemma evalRat_C {A σ : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → ℚ) (a : A) : evalRat v (C a) = a := by
  simp only [evalRat,AlgHom.restrictScalars_apply,aeval_C,Algebra.algebraMap_self,RingHom.id_apply]

@[simp] lemma evalRat_X {A σ : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → ℚ) (i : σ) : evalRat v (X i : MvPolynomial σ A) = algebraMap ℚ A (v i) := by
  simp only [evalRat,AlgHom.restrictScalars_apply,aeval_X]

@[simp] lemma evalRat_monomial {A σ : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → ℚ) (s : σ →₀ ℕ) (a : A) :
    evalRat v (monomial s a) = (s.prod fun i n => v i ^ n) • a := by
  simp only [evalRat,AlgHom.restrictScalars_apply,aeval_monomial,Algebra.algebraMap_self]
  simp only [RingHom.id_apply,Algebra.smul_def,Finsupp.prod,map_prod,map_pow]
  exact mul_comm _ _

lemma evalRat_mapLinear {A B σ : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (l : A →ₗ[ℚ] B)
    (p : MvPolynomial σ A) (v : σ → ℚ) :
    evalRat v (mapLinear l p) = l (evalRat v p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial s a => rw [mapLinear_monomial,evalRat_monomial,evalRat_monomial,map_smul]

theorem eq_of_evalRat {A σ : Type*} [CommRing A] [Algebra ℚ A]
    {p q : MvPolynomial σ A} (h : ∀ v : σ → ℚ, evalRat v p = evalRat v q) : p = q := by
  apply sub_eq_zero.mp
  have hzero : ∀ v : σ → ℚ, evalRat v (p-q)=0 := by
    intro v
    rw [map_sub,h v,sub_self]
  ext s
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro l
  have hp : mapLinear l (p-q) = 0 := by
    apply MvPolynomial.funext
    intro v
    have ht := evalRat_mapLinear l (p-q) v
    rw [hzero,map_zero] at ht
    simpa only [evalRat,AlgHom.restrictScalars_apply,aeval_def,Algebra.algebraMap_self,
      RingHom.id_apply,coe_eval₂Hom,MvPolynomial.eval,eval₂_zero] using ht
  have he := congrArg (fun polynomial => AddMonoidAlgebra.coeff polynomial s) hp
  simpa only [coeff_mapLinear, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using he

end ElementaryPositivity.CenterCalculus

namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {A α : Type*} [CommRing A]

noncomputable def toRelative : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A →ₐ[A]
    MvPolynomial (Unit ⊕ α) (Polynomial A) :=
  aeval (fun i => match i with
    | Sum.inl (Sum.inl _) => C Polynomial.X + X (Sum.inl ())
    | Sum.inl (Sum.inr _) => X (Sum.inl ())
    | Sum.inr i => X (Sum.inr i))

noncomputable def fromRelative : MvPolynomial (Unit ⊕ α) (Polynomial A) →+*
    MvPolynomial ((Unit ⊕ Unit) ⊕ α) A :=
  eval₂Hom (Polynomial.aeval (X (Sum.inl (Sum.inl ())) - X (Sum.inl (Sum.inr ())))).toRingHom
    (fun i => match i with
      | Sum.inl _ => X (Sum.inl (Sum.inr ()))
      | Sum.inr i => X (Sum.inr i))

@[simp] lemma toRelative_C (a : A) :
    toRelative (C a : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A) = C (Polynomial.C a) := by
  simp [toRelative]

@[simp] lemma toRelative_first :
    toRelative (X (Sum.inl (Sum.inl ())) : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A) =
      C Polynomial.X + X (Sum.inl ()) := by simp [toRelative]

@[simp] lemma toRelative_second :
    toRelative (X (Sum.inl (Sum.inr ())) : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A) =
      X (Sum.inl ()) := by simp [toRelative]

@[simp] lemma toRelative_other (i : α) :
    toRelative (X (Sum.inr i) : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A) = X (Sum.inr i) := by
  simp [toRelative]

@[simp] lemma fromRelative_C (p : Polynomial A) :
    fromRelative (C p : MvPolynomial (Unit ⊕ α) (Polynomial A)) =
      Polynomial.aeval (X (Sum.inl (Sum.inl ())) - X (Sum.inl (Sum.inr ()))) p := by
  simp [fromRelative]

@[simp] lemma fromRelative_common :
    fromRelative (X (Sum.inl ()) : MvPolynomial (Unit ⊕ α) (Polynomial A)) =
      X (Sum.inl (Sum.inr ())) := by simp [fromRelative]

@[simp] lemma fromRelative_other (i : α) :
    fromRelative (X (Sum.inr i) : MvPolynomial (Unit ⊕ α) (Polynomial A)) = X (Sum.inr i) := by
  simp [fromRelative]

@[simp] lemma fromRelative_toRelative (p : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A) :
    fromRelative (toRelative p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [toRelative_C,fromRelative_C,Polynomial.aeval_C,algebraMap_eq]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    rw [map_mul,map_mul,hp]
    apply congrArg (p * ·)
    rcases i with (u | u) | i
    · cases u; simp
    · cases u; simp
    · simp

theorem diagonal_dvd_of_relative_coeff (p : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A)
    (n : ℕ) (h : ∀ z s, s < n → ((toRelative p).coeff z).coeff s = 0) :
    (X (Sum.inl (Sum.inl ())) - X (Sum.inl (Sum.inr ()))) ^ n ∣ p := by
  have hd : C (Polynomial.X ^ n) ∣ toRelative p := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro z
    exact Polynomial.X_pow_dvd_iff.mpr (h z)
  have he := map_dvd fromRelative hd
  simpa only [fromRelative_C,map_pow,Polynomial.aeval_X,
    fromRelative_toRelative] using he

def relativePoint (t : ℚ) (v : Unit ⊕ α → ℚ) : (Unit ⊕ Unit) ⊕ α → ℚ
  | Sum.inl (Sum.inl _) => t + v (Sum.inl ())
  | Sum.inl (Sum.inr _) => v (Sum.inl ())
  | Sum.inr i => v (Sum.inr i)

variable [Algebra ℚ A]

lemma polynomial_eval_rat_algebraMap (r t : ℚ) :
    Polynomial.eval (algebraMap ℚ A t) (algebraMap ℚ (Polynomial A) r) = algebraMap ℚ A r := by
  exact Polynomial.eval_C

lemma evalRat_toRelative (p : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A)
    (v : Unit ⊕ α → ℚ) (t : ℚ) :
    (evalRat v (toRelative p)).eval (algebraMap ℚ A t) = evalRat (relativePoint t v) p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [toRelative_C,evalRat_C,Polynomial.eval_C,evalRat_C]
  | add p q hp hq => simp only [map_add,Polynomial.eval_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,Polynomial.eval_mul,hp]
    apply congrArg (evalRat (relativePoint t v) p * ·)
    rcases i with (u | u) | i
    · cases u
      simp only [toRelative_first,map_add,evalRat_C,evalRat_X,Polynomial.eval_add,
        Polynomial.eval_X,polynomial_eval_rat_algebraMap,relativePoint]
    · cases u
      simp only [toRelative_second,evalRat_X,polynomial_eval_rat_algebraMap,relativePoint]
    · simp only [toRelative_other,evalRat_X,polynomial_eval_rat_algebraMap,relativePoint]

end ElementaryPositivity.CenterCalculus

end

end OAI
