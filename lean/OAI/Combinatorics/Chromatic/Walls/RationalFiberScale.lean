import Mathlib

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open Polynomial
noncomputable section
open scoped LaurentSeries RatFunc
variable {K : Type*} [Field K]
def polynomialScale (a : Kˣ) : K[X] ≃ₐ[K] K[X] :=
  Polynomial.algEquivOfCompEqX (C (a:K)*X) (C (↑(a⁻¹):K)*X)
    (by simp [Polynomial.mul_comp,←mul_assoc,←map_mul])
    (by simp [Polynomial.mul_comp,←mul_assoc,←map_mul])
@[simp] lemma polynomialScale_apply (a : Kˣ) (f : K[X]) :
    polynomialScale a f=f.comp (C (a:K)*X) := by
  simp [polynomialScale,Polynomial.comp_eq_aeval]
def scaleEval (a : Kˣ) : K[X] →+* RatFunc K :=
  (algebraMap K[X] (RatFunc K)).comp (polynomialScale a).toRingHom
lemma scaleEval_injective (a : Kˣ) : Function.Injective (scaleEval a) :=
  (RatFunc.algebraMap_injective (K:=K)).comp (polynomialScale a).injective
lemma scaleEval_regular (a : Kˣ) :
    (nonZeroDivisors K[X]) ≤ (nonZeroDivisors (RatFunc K)).comap (scaleEval a) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (scaleEval_injective a)
def scale (a : Kˣ) : RatFunc K →+* RatFunc K :=
  RatFunc.liftRingHom (scaleEval a) (scaleEval_regular a)
@[simp] lemma scale_polynomial (a : Kˣ) (f : K[X]) :
    scale a (algebraMap K[X] (RatFunc K) f)=
      algebraMap K[X] (RatFunc K) (f.comp (C (a:K)*X)) := by
  rw [scale,RatFunc.liftRingHom_algebraMap]
  simp [scaleEval]
lemma ratFunc_hom_ext {L : Type*} [Field L] (f g : RatFunc K →+* L)
    (hpoly : ∀p : K[X],f (algebraMap K[X] (RatFunc K) p)=g (algebraMap K[X] (RatFunc K) p)) : f=g := by
  apply RingHom.ext
  intro x
  induction x using RatFunc.induction_on with
  | f p q hq=>simp only [map_div₀,hpoly]
@[simp] lemma scale_one : scale (1:Kˣ)=RingHom.id (RatFunc K) := by
  apply ratFunc_hom_ext
  intro p
  simp
lemma scale_mul (a b : Kˣ) : (scale a).comp (scale b)=scale (a*b) := by
  apply ratFunc_hom_ext
  intro p
  simp only [RingHom.comp_apply,scale_polynomial]
  congr 1
  rw [Polynomial.comp_assoc]
  congr 1
  simp only [Polynomial.mul_comp,Polynomial.C_comp,Polynomial.X_comp,Units.val_mul]
  rw [←mul_assoc,←map_mul,mul_comm (b:K) (a:K)]
@[simp] lemma scale_constant (a : Kˣ) (b : K) :
    scale a (RatFunc.C b)=RatFunc.C b := by
  change scale a (algebraMap K[X] (RatFunc K) (C b))=algebraMap K[X] (RatFunc K) (C b)
  rw [scale_polynomial,Polynomial.C_comp]
@[simp] lemma scale_X (a : Kˣ) : scale a RatFunc.X=RatFunc.C (a:K)*RatFunc.X := by
  change scale a (algebraMap K[X] (RatFunc K) X)=_
  rw [scale_polynomial,Polynomial.X_comp,map_mul]
  rfl
def scaleEquiv (a : Kˣ) : RatFunc K ≃+* RatFunc K :=
  RingEquiv.ofRingHom (scale a) (scale a⁻¹)
    (by rw [scale_mul,mul_inv_cancel,scale_one])
    (by rw [scale_mul,inv_mul_cancel,scale_one])

def expandZero : RatFunc K →+* LaurentSeries K := algebraMap _ _
lemma expandZero_injective : Function.Injective (expandZero (K:=K)) := (expandZero (K:=K)).injective
end
end ElementaryPositivity.RationalFiber

end

end OAI
