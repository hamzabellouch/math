import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

def cornerSubalgebra : NonUnitalStarSubalgebra ℂ A where
  carrier := {a | p*a=a ∧ a*p=a}
  zero_mem' := by simp
  add_mem' := by rintro a b ⟨ha, ha'⟩ ⟨hb,hb'⟩; simp [mul_add, add_mul, ha, ha', hb, hb']
  mul_mem' := by rintro a b ⟨ha, ha'⟩ ⟨hb,hb'⟩; exact ⟨by rw [←mul_assoc, ha], by rw [mul_assoc, hb']⟩
  smul_mem' := by rintro c a ⟨ha,ha'⟩; simp [ha, ha']
  star_mem' := by
    rintro a ⟨ha,ha'⟩
    constructor
    · simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star ha'
    · simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star ha

def Corner : Type _ := ↥(cornerSubalgebra hp)

instance : CoeOut (Corner hp) A := ⟨Subtype.val⟩

instance : Ring (Corner hp) where
  __ : NonUnitalRing (Corner hp) := inferInstanceAs (NonUnitalRing (cornerSubalgebra hp))
  one := ⟨p, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq⟩
  one_mul a := Subtype.ext a.property.1
  mul_one a := Subtype.ext a.property.2

instance : NormedRing (Corner hp) where
  __ : Ring (Corner hp) := inferInstance
  __ : NonUnitalNormedRing (Corner hp) := inferInstanceAs (NonUnitalNormedRing (cornerSubalgebra hp))

instance : StarRing (Corner hp) := inferInstanceAs (StarRing (cornerSubalgebra hp))

instance : Module ℂ (Corner hp) := inferInstanceAs (Module ℂ (cornerSubalgebra hp))

instance : NormedSpace ℂ (Corner hp) := inferInstanceAs (NormedSpace ℂ (cornerSubalgebra hp))

instance : IsScalarTower ℂ (Corner hp) (Corner hp) :=
  inferInstanceAs (IsScalarTower ℂ (cornerSubalgebra hp) (cornerSubalgebra hp))

instance : SMulCommClass ℂ (Corner hp) (Corner hp) :=
  inferInstanceAs (SMulCommClass ℂ (cornerSubalgebra hp) (cornerSubalgebra hp))

instance : Algebra ℂ (Corner hp) := Algebra.ofModule smul_mul_assoc mul_smul_comm

instance : NormedAlgebra ℂ (Corner hp) where
  norm_smul_le := norm_smul_le

instance : StarModule ℂ (Corner hp) := inferInstanceAs (StarModule ℂ (cornerSubalgebra hp))

instance : CStarRing (Corner hp) where
  norm_mul_self_le x := (CStarRing.norm_star_mul_self (x := (x : A))).symm.le

lemma cornerSubalgebra_closed : IsClosed ((cornerSubalgebra hp : NonUnitalStarSubalgebra ℂ A) : Set A) :=
  (isClosed_eq (by fun_prop : Continuous (fun a : A => p*a)) continuous_id).inter
    (isClosed_eq (by fun_prop : Continuous (fun a : A => a*p)) continuous_id)

instance : CompleteSpace (Corner hp) := (cornerSubalgebra_closed hp).completeSpace_coe

instance : CStarAlgebra (Corner hp) where

@[simp] lemma corner_one : ((1 : Corner hp) : A) = p := rfl

@[simp] lemma corner_add (a b : Corner hp) : ((a+b : Corner hp) : A) = (a : A)+(b : A) := rfl

@[simp] lemma corner_mul (a b : Corner hp) : ((a*b : Corner hp) : A) = (a : A)*(b : A) := rfl

@[simp] lemma corner_star (a : Corner hp) : ((star a : Corner hp) : A) = star (a : A) := rfl

@[simp] lemma corner_norm (a : Corner hp) : ‖a‖=‖(a : A)‖ := rfl

end Kadison

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

instance cornerOrder : PartialOrder (Corner hp) := CStarAlgebra.spectralOrder (Corner hp)

instance cornerStarOrdered : StarOrderedRing (Corner hp) := CStarAlgebra.spectralOrderedRing (Corner hp)

def cornerInclusion : Corner hp →⋆ₙₐ[ℂ] A := NonUnitalStarSubalgebraClass.subtype (cornerSubalgebra hp)

@[simp] lemma cornerInclusion_apply (a : Corner hp) : cornerInclusion hp a = (a : A) := rfl

variable [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder

def cornerFunctional (τ : A →ₚ[ℂ] ℂ) (r : ℝ) (hr : 0<r) : Corner hp →ₚ[ℂ] ℂ where
  toLinearMap := r⁻¹ • (τ.toLinearMap.comp (cornerSubalgebra hp).toSubmodule.subtype)
  monotone' := by
    intro a b hab
    have hc : (a : A) ≤ (b : A) :=
      @NonUnitalStarRingHom.map_le_map_of_map_star (Corner hp) A _ (cornerOrder hp)
        _ (cornerStarOrdered hp) _ _ _ _ (NonUnitalStarRingHom.ofClass (cornerInclusion hp)) a b hab
    exact smul_le_smul_of_nonneg_left (τ.monotone hc) (inv_nonneg.mpr hr.le)

@[simp] lemma cornerFunctional_apply (τ : A →ₚ[ℂ] ℂ) {r : ℝ} (hr : 0<r) (a : Corner hp) :
    cornerFunctional hp τ r hr a = r⁻¹ • τ (a : A) := rfl

lemma cornerFunctional_normalized (τ : A →ₚ[ℂ] ℂ) {r : ℝ} (hr : 0<r)
    (hτ : τ p = (r : ℂ)) : cornerFunctional hp τ r hr 1=1 := by
  simp only [cornerFunctional_apply, corner_one, hτ, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one]

lemma cornerFunctional_tracial (τ : A →ₚ[ℂ] ℂ) {r : ℝ} (hr : 0<r)
    (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (a b : Corner hp) :
    cornerFunctional hp τ r hr (a*b)=cornerFunctional hp τ r hr (b*a) := by
  simp only [cornerFunctional_apply, corner_mul, hτ (a : A) (b : A)]

lemma cornerFunctional_faithful (τ : A →ₚ[ℂ] ℂ) {r : ℝ} (hr : 0<r)
    (hτ : ∀ a : A, τ (star a*a)=0 → a=0) (a : Corner hp)
    (ha : cornerFunctional hp τ r hr (star a*a)=0) : a=0 := by
  apply Subtype.ext
  apply hτ
  simpa only [cornerFunctional_apply, corner_mul, corner_star,
    smul_eq_zero, inv_eq_zero, hr.ne', false_or] using ha

end Kadison

end

end
end

end OAI
