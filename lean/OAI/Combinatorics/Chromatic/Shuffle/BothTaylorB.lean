import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.Eval
import OAI.Combinatorics.Chromatic.Walls.PolynomialCoeffLinear

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma polynomial_eq_of_rat_evals {A : Type*} [CommRing A] [Algebra ℚ A]
    (p q : Polynomial A) (h : ∀ t : ℚ,p.eval (algebraMap ℚ A t)=q.eval (algebraMap ℚ A t)) :
    p=q := by
  have hz : p-q=0 := by
    ext n
    have hn := ElementaryPositivity.CommonTranslation.polynomial_coeff_mem (⊥ : Submodule ℚ A)
      (p-q) (by intro t; simp [Polynomial.eval_sub,h t]) n
    simpa only [Submodule.mem_bot,Polynomial.coeff_zero] using hn
  exact sub_eq_zero.mp hz

lemma taylorB_eval (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f : B a μ d) (t : ℚ) :
    (taylorB a μ d f).eval (algebraMap ℚ (B a μ d) t)=translationB a μ d t f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change (taylorB a μ d (quotientAlg a μ d f)).eval _ =
      quotientAlg a μ d (translationS d t f)
    rw [taylorB_mk,eval_map_rat,taylorS_eval]

omit [Fintype I] [DecidableEq I] in
lemma tensorValue_translation (d e : I → ℕ) (t : ℚ) (x : S d ⊗[ℚ] S e) :
    tensorValue d e (TensorProduct.map (translationS d t) (translationS e t) x)=
      translation t (tensorValue d e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul f g =>
    simp only [TensorProduct.map_tmul,tensorValue_tmul,map_mul,translation_rename]
    rfl
  | add x y hx hy => simp only [map_add,hx,hy]

lemma restrictTensor_translation {d e : I → ℕ} (A : Cut d e) (t : ℚ) (f : S (d+e)) :
    restrictTensor A (translationS (d+e) t f)=
      TensorProduct.map (translationS d t) (translationS e t) (restrictTensor A f) := by
  apply tensorValue_injective
  rw [tensorValue_translation,tensorValue_restrictTensor,tensorValue_restrictTensor,translation_rename]
  rfl

lemma restrictionB_translation (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (A : Cut d e) (t : ℚ) (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    restrictionB a c η hc hs A (translationB a (SlopeArithmetic.slope c η) (d+e) t f)=
      TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d t)
        (translationB a (SlopeArithmetic.slope c η) e t) (restrictionB a c η hc hs A f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change restrictionB a c η hc hs A (quotientAlg a _ (d+e) (translationS (d+e) t f))=
      TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d t)
        (translationB a (SlopeArithmetic.slope c η) e t)
          (restrictionB a c η hc hs A (quotientAlg a _ (d+e) f))
    rw [restrictionB_mk,restrictionB_mk,restrictTensor_translation]
    generalize restrictTensor A f=x
    induction x using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add,hx,hy]

@[simp] lemma polynomialMapLinear_monomial {A D : Type*} [CommRing A] [CommRing D]
    [Algebra ℚ A] [Algebra ℚ D] (l : A →ₗ[ℚ] D) (n : ℕ) (a : A) :
    polynomialMapLinear l (Polynomial.monomial n a)=Polynomial.monomial n (l a) := by
  ext m
  simp only [polynomialMapLinear_coeff,Polynomial.coeff_monomial]
  split_ifs <;> simp

lemma polynomialMapLinear_eval_rat {A D : Type*} [CommRing A] [CommRing D]
    [Algebra ℚ A] [Algebra ℚ D] (l : A →ₗ[ℚ] D) (p : Polynomial A) (t : ℚ) :
    (polynomialMapLinear l p).eval (algebraMap ℚ D t)=l (p.eval (algebraMap ℚ A t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,Polynomial.eval_add,hp,hq]
  | monomial n a =>
    rw [polynomialMapLinear_monomial,Polynomial.eval_monomial,Polynomial.eval_monomial]
    rw [← map_pow,← map_pow,mul_comm (l a),mul_comm a,← Algebra.smul_def,← Algebra.smul_def,map_smul]

noncomputable def bothTaylorB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    B a μ d ⊗[ℚ] B a μ e →ₐ[ℚ] Polynomial (Polynomial (B a μ d ⊗[ℚ] B a μ e)) :=
  let L : B a μ d →ₐ[ℚ] Polynomial (Polynomial (B a μ d ⊗[ℚ] B a μ e)) := (Polynomial.CAlgHom : Polynomial (B a μ d ⊗[ℚ] B a μ e) →ₐ[ℚ] Polynomial (Polynomial (B a μ d ⊗[ℚ] B a μ e))).comp
    ((Polynomial.mapAlgHom (Algebra.TensorProduct.includeLeft :
      B a μ d →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e)).comp (taylorB a μ d))
  let R : B a μ e →ₐ[ℚ] Polynomial (Polynomial (B a μ d ⊗[ℚ] B a μ e)) := (Polynomial.mapAlgHom ((Polynomial.CAlgHom : (B a μ d ⊗[ℚ] B a μ e) →ₐ[ℚ] Polynomial (B a μ d ⊗[ℚ] B a μ e)).comp
    (Algebra.TensorProduct.includeRight : B a μ e →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e))).comp (taylorB a μ e)
  Algebra.TensorProduct.lift (S:=ℚ) L R (by
    let : CommRing (Polynomial (B a μ d ⊗[ℚ] B a μ e)) := inferInstance
    intro x y
    exact mul_comm (L x) (R y))

noncomputable def evalTwo {A : Type*} [CommRing A] [Algebra ℚ A]
    (p : Polynomial (Polynomial A)) (z w : ℚ) : A :=
  (p.eval (algebraMap ℚ (Polynomial A) w)).eval (algebraMap ℚ A z)

lemma bothTaylorB_eval (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : B a μ d ⊗[ℚ] B a μ e) (z w : ℚ) :
    evalTwo (bothTaylorB a μ d e x) z w=
      TensorProduct.map (translationB a μ d z) (translationB a μ e w) x := by
  induction x using TensorProduct.inductionOn with
  | tmul f g =>
    change evalTwo
      (Polynomial.C (Polynomial.map (Algebra.TensorProduct.includeLeft :
        B a μ d →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e).toRingHom (taylorB a μ d f)) *
        Polynomial.map ((Polynomial.CAlgHom : (B a μ d ⊗[ℚ] B a μ e) →ₐ[ℚ] Polynomial (B a μ d ⊗[ℚ] B a μ e)).comp
          (Algebra.TensorProduct.includeRight : B a μ e →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e)).toRingHom
          (taylorB a μ e g)) z w = _
    simp only [evalTwo,Polynomial.eval_mul,Polynomial.eval_C,eval_map_rat,taylorB_eval,
      AlgHom.comp_apply,Polynomial.CAlgHom_apply,Polynomial.eval_C,TensorProduct.map_tmul]
    change (translationB a μ d z f ⊗ₜ[ℚ] 1)*(1 ⊗ₜ[ℚ] translationB a μ e w g)=_
    rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  | add x y hx hy => simp only [map_add,evalTwo,Polynomial.eval_add] at *; rw [hx,hy]

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma relativeTaylorB_eval (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : B a μ d ⊗[ℚ] B a μ e) (z : ℚ) :
    (relativeTaylorB a μ d e x).eval (algebraMap ℚ (B a μ d ⊗[ℚ] B a μ e) z)=
      TensorProduct.map (translationB a μ d z) (LinearMap.id : B a μ e →ₗ[ℚ] B a μ e) x := by
  induction x using TensorProduct.inductionOn with
  | tmul f g =>
    change (Polynomial.map (Algebra.TensorProduct.includeLeft :
      B a μ d →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e).toRingHom (taylorB a μ d f) *
      Polynomial.C (1 ⊗ₜ[ℚ] g)).eval _ = _
    rw [Polynomial.eval_mul,eval_map_rat,taylorB_eval,Polynomial.eval_C]
    change (translationB a μ d z f ⊗ₜ[ℚ] 1)*(1 ⊗ₜ[ℚ] g)=_
    rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
    rfl
  | add x y hx hy => simp only [map_add,Polynomial.eval_add,hx,hy]

lemma evalTwo_ext {A : Type*} [CommRing A] [Algebra ℚ A]
    (p q : Polynomial (Polynomial A)) (h : ∀ z w : ℚ,evalTwo p z w=evalTwo q z w) : p=q := by
  apply polynomial_eq_of_rat_evals
  intro w
  apply polynomial_eq_of_rat_evals
  intro z
  exact h z w

noncomputable def bothLeading (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (p q : ℤ) : B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      Polynomial (Polynomial (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e)) :=
  (polynomialMapLinear (polynomialMapLinear (TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d p)
    (componentB a (SlopeArithmetic.slope c η) e q)))).comp
      ((bothTaylorB a (SlopeArithmetic.slope c η) d e).toLinearMap.comp
        (restrictionB a c η hc hs (firstCut d e)).toLinearMap)

noncomputable def commonRelativeLeading (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (p q : ℤ) : B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      Polynomial (Polynomial (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e)) :=
  (polynomialMapLinear (R:=B a (SlopeArithmetic.slope c η) (d+e))
    (S:=Polynomial (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e))
    (relativeLeading a c η hc (d:=d) (e:=e) hs p q)).comp
    (taylorB a (SlopeArithmetic.slope c η) (d+e)).toLinearMap

lemma bothLeading_eval (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (p q : ℤ) (f : B a (SlopeArithmetic.slope c η) (d+e)) (z w : ℚ) :
    evalTwo (bothLeading a c η hc hs p q f) z w =
      TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d p)
        (componentB a (SlopeArithmetic.slope c η) e q)
        (TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d z)
          (translationB a (SlopeArithmetic.slope c η) e w)
          (restrictionB a c η hc hs (firstCut d e) f)) := by
  simp only [bothLeading,LinearMap.comp_apply,AlgHom.toLinearMap_apply,evalTwo,
    polynomialMapLinear_eval_rat]
  rw [← evalTwo,bothTaylorB_eval]

lemma commonRelativeLeading_eval (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (p q : ℤ) (f : B a (SlopeArithmetic.slope c η) (d+e)) (z w : ℚ) :
    evalTwo (commonRelativeLeading a c η hc hs p q f) z w =
      TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d p)
        (componentB a (SlopeArithmetic.slope c η) e q)
        (TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d z)
          (LinearMap.id : B a (SlopeArithmetic.slope c η) e →ₗ[ℚ] B a (SlopeArithmetic.slope c η) e)
          (restrictionB a c η hc hs (firstCut d e)
            (translationB a (SlopeArithmetic.slope c η) (d+e) w f))) := by
  simp only [commonRelativeLeading,LinearMap.comp_apply,AlgHom.toLinearMap_apply,evalTwo,
    polynomialMapLinear_eval_rat,taylorB_eval]
  simp only [relativeLeading,LinearMap.comp_apply,AlgHom.toLinearMap_apply,
    polynomialMapLinear_eval_rat,relativeTaylorB_eval]

lemma bothLeading_relative (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (p q : ℤ) (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    IndependentCenters.plus (bothLeading a c η hc hs p q f)=
      commonRelativeLeading a c η hc hs p q f := by
  apply evalTwo_ext
  intro z w
  change IndependentCenters.eval z w (IndependentCenters.plus _) = _
  rw [IndependentCenters.eval_plus]
  change evalTwo (bothLeading a c η hc hs p q f) (z+w) w = _
  rw [bothLeading_eval,commonRelativeLeading_eval,restrictionB_translation]
  congr 1
  generalize restrictionB a c η hc hs (firstCut d e) f=x
  induction x using TensorProduct.inductionOn with
  | tmul x y => simp only [TensorProduct.map_tmul,LinearMap.id_apply,translationB_add]
  | add x y hx hy => simp only [map_add,hx,hy]

theorem bothLeading_diagonal_divisible (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hd : d≠0) (he : e≠0)
    (hdθ : SlopeArithmetic.slope c η d=θ) (heθ : SlopeArithmetic.slope c η e=θ)
    (hsym : eulerForm a d e=eulerForm a e d) (p q W : ℤ)
    (hw : 2*(p+q)+eulerForm a d d+eulerForm a e e=W)
    (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    IndependentCenters.DiagonalDivides (-eulerForm a d e).toNat
      (bothLeading a c η hc (d:=d) (e:=e) (hdθ.trans heθ.symm) p q f) := by
  let : CommRing (Polynomial (B a (SlopeArithmetic.slope c η) d ⊗[ℚ]
    B a (SlopeArithmetic.slope c η) e)) := inferInstance
  apply IndependentCenters.diagonalDivides_of_relative
  rw [bothLeading_relative]
  apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
  intro r
  change Polynomial.X^(-eulerForm a d e).toNat ∣
    relativeLeading a c η hc (hdθ.trans heθ.symm) p q ((taylorB a (SlopeArithmetic.slope c η) (d+e) f).coeff r)
  exact relativeLeading_taylor_divisible a c η hc θ d e hd he hdθ heθ r hsym p q W hw f hf

end ElementaryPositivity.RawShuffle

end

end OAI
