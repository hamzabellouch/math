import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RationalFiberScale

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
open scoped LaurentSeries RatFunc
variable {K : Type*} [Field K]
lemma ratFunc_hom_ext_C_X {L : Type*} [Field L] (f g : RatFunc K →+* L)
    (hc : ∀a : K,f (RatFunc.C a)=g (RatFunc.C a)) (hx : f RatFunc.X=g RatFunc.X) : f=g := by
  apply ratFunc_hom_ext
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>simp only [map_add,hp,hq]
  | monomial n a=>
    simp only [←Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,RatFunc.algebraMap_C,RatFunc.algebraMap_X,hc,hx]
lemma reciprocal_transcendental : Transcendental K ((RatFunc.X : RatFunc K)⁻¹) := by
  intro h
  exact RatFunc.transcendental_X (IsAlgebraic.inv_iff.mp h)
def reciprocalEval : Polynomial K →ₐ[K] RatFunc K :=
  Polynomial.aeval ((RatFunc.X : RatFunc K)⁻¹)
lemma reciprocalEval_injective : Function.Injective (reciprocalEval (K:=K)) :=
  transcendental_iff_injective.mp reciprocal_transcendental
lemma reciprocalEval_regular :
    (nonZeroDivisors (Polynomial K)) ≤ (nonZeroDivisors (RatFunc K)).comap reciprocalEval :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ reciprocalEval_injective
def reciprocal : RatFunc K →+* RatFunc K :=
  RatFunc.liftRingHom reciprocalEval.toRingHom reciprocalEval_regular
@[simp] lemma reciprocal_polynomial (f : Polynomial K) :
    reciprocal (algebraMap (Polynomial K) (RatFunc K) f)=reciprocalEval f :=
  RatFunc.liftRingHom_algebraMap _ _ _
@[simp] lemma reciprocal_X : reciprocal RatFunc.X=(RatFunc.X : RatFunc K)⁻¹ := by
  change reciprocal (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=_
  rw [reciprocal_polynomial]
  simp [reciprocalEval]
@[simp] lemma reciprocal_constant (a : K) : reciprocal (RatFunc.C a)=RatFunc.C a := by
  rw [←RatFunc.algebraMap_C,reciprocal_polynomial]
  simp [reciprocalEval]
lemma reciprocal_involutive : (reciprocal (K:=K)).comp reciprocal=RingHom.id _ := by
  apply ratFunc_hom_ext_C_X <;> simp
lemma reciprocal_scale (a : Kˣ) :
    (reciprocal (K:=K)).comp (scale a)=(scale a⁻¹).comp reciprocal := by
  apply ratFunc_hom_ext_C_X
  · intro b; simp
  · simp [mul_inv_rev,mul_comm]
def reciprocalEquiv : RatFunc K ≃+* RatFunc K :=
  RingEquiv.ofRingHom reciprocal reciprocal reciprocal_involutive reciprocal_involutive
def expandInfinity : RatFunc K →+* LaurentSeries K := expandZero.comp reciprocal
lemma expandInfinity_injective : Function.Injective (expandInfinity (K:=K)) :=
  (expandInfinity (K:=K)).injective
@[simp] lemma expandZero_X : expandZero (RatFunc.X : RatFunc K)=HahnSeries.single (1:ℤ) 1 :=
  RatFunc.coe_X
@[simp] lemma expandZero_constant (a : K) : expandZero (RatFunc.C a)=HahnSeries.C a := by
  change algebraMap (RatFunc K) (LaurentSeries K) (RatFunc.C a)=_
  rw [←RatFunc.algebraMap_C,←IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
  simp
@[simp] lemma expandZero_X_zpow (n : ℤ) :
    expandZero ((RatFunc.X : RatFunc K)^n)=HahnSeries.single n 1 := by
  rw [map_zpow₀,expandZero_X,←RatFunc.single_zpow]
@[simp] lemma expandInfinity_X_zpow (n : ℤ) :
    expandInfinity ((RatFunc.X : RatFunc K)^n)=HahnSeries.single (-n) 1 := by
  change expandZero (reciprocal ((RatFunc.X : RatFunc K)^n))=_
  rw [map_zpow₀,reciprocal_X,inv_zpow,←zpow_neg,expandZero_X_zpow]
end
end ElementaryPositivity.RationalFiber

end

end OAI
