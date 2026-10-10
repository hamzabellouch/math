import Mathlib
import OAI.Combinatorics.Chromatic.Walls.QuantumTorusRaySeries

namespace OAI

section
section
namespace ElementaryPositivity.WallUnits
open PowerSeries
noncomputable section
namespace PositiveRay
lemma positive_rescale (b : ℤ) (F : PowerSeries (RatFunc ℚ)) (hF : Positive F) :
    Positive (PowerSeries.rescale (RationalRay.v^b) F) := by
  obtain ⟨A,rfl⟩:=hF
  refine ⟨PowerSeries.rescale (LaurentPolynomial.T b) A,?_⟩
  apply PowerSeries.ext
  intro n
  simp only [coeff_map,coeff_rescale,map_mul,map_pow,eval_T]
end PositiveRay

namespace RationalRay
lemma reverse_ratio (F G : PowerSeries (RatFunc ℚ)) (t : ℕ) :
    PowerSeries.rescale (q^t) G * F=
      PowerSeries.rescale (q^t) (PowerSeries.rescale (q⁻¹^t) F * G) := by
  rw [map_mul,PowerSeries.rescale_rescale,←mul_pow,inv_mul_cancel₀ q_nonzero,one_pow,
    PowerSeries.rescale_one,RingHom.id_apply,mul_comm]
lemma elementary_inverse_ratio_positive (k : ℤ) (t : ℕ) :
    PositiveRay.Positive (PowerSeries.rescale (q^t) (elementary q (v^k))⁻¹ * elementary q (v^k)) := by
  rw [reverse_ratio,q_pow]
  exact PositiveRay.positive_rescale _ _ (elementary_ratio_positive k t)
lemma complete_inverse_ratio_positive (k : ℤ) (t : ℕ) :
    PositiveRay.Positive (PowerSeries.rescale (q^t) (elementary q (-(v^k))) * complete q (v^k)) := by
  rw [reverse_ratio,q_pow]
  exact PositiveRay.positive_rescale _ _ (complete_ratio_positive k t)
end RationalRay
end
end ElementaryPositivity.WallUnits
end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ)
local instance wallUnitNegativePositiveAddGroup : AddGroup (Torus PositiveRay.vUnit Ω) := (Torus.instRing PositiveRay.vUnit Ω).toAddGroup

lemma positive_elementary_inverse_adjoint (hΩ : ∀m,Ω m m=0) (a m : M) (k : ℤ) (t : ℕ)
    (ht : Ω a m= -(t:ℤ)) :
    PositiveCoefficients Ω (
      (rayUnit PositiveRay.vUnit Ω a (hΩ a) (elementary RationalRay.q (RationalRay.v^k))
        (constant_elementary _ _)).inv * PowerSeries.C (Torus.X PositiveRay.vUnit Ω m) *
      (rayUnit PositiveRay.vUnit Ω a (hΩ a) (elementary RationalRay.q (RationalRay.v^k))
        (constant_elementary _ _)).val) := by
  rw [ray_inverse_adjoint PositiveRay.vUnit Ω hΩ]
  apply positive_monomial_ray
  have he : (↑(PositiveRay.vUnit^(2*Ω a m)):RatFunc ℚ)=RationalRay.q^t := by
    rw [ht,RationalRay.q_pow,Units.val_zpow_eq_zpow_val]
    change RationalRay.v^(2* -(t:ℤ))=RationalRay.v^(-2*(t:ℤ))
    congr 1
    ring
  rw [he]
  exact RationalRay.elementary_inverse_ratio_positive k t

lemma positive_complete_inverse_adjoint (hΩ : ∀m,Ω m m=0) (a m : M) (k : ℤ) (t : ℕ)
    (ht : Ω a m= -(t:ℤ)) :
    PositiveCoefficients Ω (
      (rayUnit PositiveRay.vUnit Ω a (hΩ a) (complete RationalRay.q (RationalRay.v^k))
        (complete_constant _ _)).inv * PowerSeries.C (Torus.X PositiveRay.vUnit Ω m) *
      (rayUnit PositiveRay.vUnit Ω a (hΩ a) (complete RationalRay.q (RationalRay.v^k))
        (complete_constant _ _)).val) := by
  rw [ray_inverse_adjoint PositiveRay.vUnit Ω hΩ]
  apply positive_monomial_ray
  have he : (↑(PositiveRay.vUnit^(2*Ω a m)):RatFunc ℚ)=RationalRay.q^t := by
    rw [ht,RationalRay.q_pow,Units.val_zpow_eq_zpow_val]
    change RationalRay.v^(2* -(t:ℤ))=RationalRay.v^(-2*(t:ℤ))
    congr 1
    ring
  rw [he,complete_inverse]
  exact RationalRay.complete_inverse_ratio_positive k t

lemma ray_constant_one {K : Type*} [Field K] (v : Kˣ) (Ω : M →+ M →+ ℤ)
    (a : M) (F : PowerSeries K) (hF : constantCoeff F=1) :
    constantCoeff (raySeries v Ω a F)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply,coeff_raySeries,zero_nsmul,
    coeff_zero_eq_constantCoeff_apply,hF]
  rfl

lemma ray_adjoint_no_jump {K : Type*} [Field K] (v : Kˣ) (Ω : M →+ M →+ ℤ)
    (a m : M) (ha : Ω a a=0) (F : PowerSeries K) (hF : constantCoeff F=1) :
    constantCoeff ((rayUnit v Ω a ha F hF).val * PowerSeries.C (Torus.X v Ω m) *
      (rayUnit v Ω a ha F hF).inv)=Torus.X v Ω m := by
  change constantCoeff (raySeries v Ω a F * PowerSeries.C (Torus.X v Ω m) * raySeries v Ω a F⁻¹)=_
  rw [map_mul,map_mul,ray_constant_one v Ω a F hF,constantCoeff_C,one_mul,
    ray_constant_one v Ω a F⁻¹ (by rw [constantCoeff_inv,hF,inv_one]),mul_one]

lemma ray_inverse_adjoint_no_jump {K : Type*} [Field K] (v : Kˣ) (Ω : M →+ M →+ ℤ)
    (a m : M) (ha : Ω a a=0) (F : PowerSeries K) (hF : constantCoeff F=1) :
    constantCoeff ((rayUnit v Ω a ha F hF).inv * PowerSeries.C (Torus.X v Ω m) *
      (rayUnit v Ω a ha F hF).val)=Torus.X v Ω m := by
  change constantCoeff (raySeries v Ω a F⁻¹ * PowerSeries.C (Torus.X v Ω m) * raySeries v Ω a F)=_
  rw [map_mul,map_mul,ray_constant_one v Ω a F⁻¹ (by rw [constantCoeff_inv,hF,inv_one]),
    constantCoeff_C,one_mul,ray_constant_one v Ω a F hF,mul_one]
end
end ElementaryPositivity.QuantumTorus
end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ)
local instance wallUnitNegativeNormalizedAddGroup : AddGroup (Torus PositiveRay.vUnit Ω) := (Torus.instRing PositiveRay.vUnit Ω).toAddGroup

section Generic
variable {R : Type*} [CommRing R] (v : Rˣ) (Ω' : M →+ M →+ ℤ)
local instance wallUnitNegativeGenericAddGroup : AddGroup (Torus v Ω') := (Torus.instRing v Ω').toAddGroup
lemma coeff_linear {A : Type*} [Ring A] (b : A) (n : ℕ) :
    coeff n (1+PowerSeries.C b*PowerSeries.X)=
      (if n=0 then 1 else 0)+b*(if n=1 then 1 else 0) := by
  rw [map_add,coeff_one,coeff_C_mul,coeff_X]
lemma ray_linear (a : M) (b : R) :
    raySeries v Ω' a (1+PowerSeries.C b*PowerSeries.X)=
      1+PowerSeries.C (Torus.monomial v Ω' a b)*PowerSeries.X := by
  apply PowerSeries.ext
  intro n
  rw [coeff_raySeries,coeff_linear]
  rw [@coeff_linear (Torus v Ω') (Torus.instRing v Ω')]
  by_cases h0 : n=0
  · subst n
    simp only [ite_true,show (0:ℕ)≠1 by omega,ite_false,mul_zero,Torus.mul_zero,add_zero,zero_nsmul]
    rfl
  by_cases h1 : n=1
  · subst n
    simp only [h0,ite_false,ite_true,mul_one,zero_add,one_nsmul]
  simp only [ite_eq_right h0,ite_eq_right h1,mul_zero,Torus.mul_zero,zero_add,Torus.monomial_zero]
end Generic

lemma normalized_constant : constantCoeff RationalRay.normalized=1 := by
  exact constant_elementary _ _

lemma normalized_ratio_one : PowerSeries.rescale RationalRay.q⁻¹ RationalRay.normalized *
    RationalRay.normalized⁻¹=1+PowerSeries.C RationalRay.v*PowerSeries.X := by
  have h:=RationalRay.normalized_ratio 1
  simp only [pow_one,Finset.prod_range_succ,Finset.prod_range_zero,one_mul,zero_add] at h
  have hs : RationalRay.v⁻¹*RationalRay.q⁻¹=RationalRay.v := by
    rw [RationalRay.q,←zpow_neg,←zpow_neg_one,←zpow_add₀ RationalRay.v_nonzero]
    norm_num
  rwa [hs] at h

lemma simple_jump (hΩ : ∀m,Ω m m=0) (a m : M) (ham : Ω a m=1) :
    (rayUnit PositiveRay.vUnit Ω a (hΩ a) RationalRay.normalized normalized_constant).val *
      PowerSeries.C (Torus.X PositiveRay.vUnit Ω m) *
    (rayUnit PositiveRay.vUnit Ω a (hΩ a) RationalRay.normalized normalized_constant).inv=
      PowerSeries.C (Torus.X PositiveRay.vUnit Ω m)+
      PowerSeries.C (Torus.X PositiveRay.vUnit Ω (m+a))*PowerSeries.X := by
  rw [ray_adjoint PositiveRay.vUnit Ω hΩ]
  have he : (↑(PositiveRay.vUnit^(2*Ω a m)):RatFunc ℚ)=RationalRay.q⁻¹ := by
    rw [ham,RationalRay.q,←zpow_neg,Units.val_zpow_eq_zpow_val]
    rfl
  rw [he,normalized_ratio_one,ray_linear,mul_add,mul_one,←mul_assoc,←map_mul]
  congr 2
  simp only [Torus.X,Torus.monomial_mul_monomial,one_mul]
  have hma : Ω m a= -1 := by rw [alternating_skew Ω hΩ m a,ham]
  rw [hma,Units.val_zpow_eq_zpow_val]
  congr 1
  change Torus.monomial PositiveRay.vUnit Ω (m+a) (RationalRay.v*RationalRay.v^(-1:ℤ))=_
  rw [zpow_neg_one,mul_inv_cancel₀ RationalRay.v_nonzero]
end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
