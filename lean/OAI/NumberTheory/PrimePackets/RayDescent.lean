import Mathlib
import OAI.NumberTheory.PrimePackets.RayEuler

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)

lemma underlyingIdeal_integralUnit (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    underlyingIdeal ⟨integralIdealFractionalUnit J hJ, FractionalIdeal.coeIdeal_le_one⟩ = J := by
  apply FractionalIdeal.coeIdeal_injective (K := K)
  exact underlyingIdeal_coe ⟨integralIdealFractionalUnit J hJ,
    FractionalIdeal.coeIdeal_le_one⟩

 

lemma coprime_inverse_product (hψ : ψ.residue = 1)
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIc : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (hJc : IsCoprime J (rationalModulusIdeal (𝓞 K) N))
    (hclass : ClassGroup.mk K (integralIdealFractionalUnit J hJ) =
      (ClassGroup.mk K (integralIdealFractionalUnit I hI))⁻¹) :
    ψ.idealHom (integralIdealFractionalUnit I hI) *
      ψ.idealHom (integralIdealFractionalUnit J hJ) = 1 := by
  let Jf : integralIdealClassFiber (integralIdealFractionalUnit I hI) :=
    ⟨integralIdealFractionalUnit J hJ, FractionalIdeal.coeIdeal_le_one, hclass⟩
  let a := idealIntegerElement I hI (idealElementRepresentative _ Jf)
  have ha : a ≠ 0 := generator_integer_ne_zero I hI Jf
  have hp : Ideal.span {a} = I * J := by
    have H := generator_principal_product I hI Jf
    change Ideal.span {a} = I * underlyingIdeal
      ⟨integralIdealFractionalUnit J hJ, FractionalIdeal.coeIdeal_le_one⟩ at H
    simpa only [underlyingIdeal_integralUnit] using H
  have hac : IsCoprime (Ideal.span {a}) (rationalModulusIdeal (𝓞 K) N) := by
    rw [hp]
    exact IsCoprime.mul_left_iff.mpr ⟨hIc, hJc⟩
  have H := ψ.principalLaw a ha hac
  rw [hψ, MulChar.one_apply ((quotient_isUnit_iff_span_coprime _ a).mpr hac)] at H
  have HG := generator_fractional_product I hI Jf
  change integralIdealFractionalUnit (Ideal.span {a}) _ =
    integralIdealFractionalUnit I hI * integralIdealFractionalUnit J hJ at HG
  rw [HG, map_mul, Units.val_mul] at H
  exact Units.ext H

variable [NeZero N]

 

theorem idealHom_eq_of_coprime_class (hψ : ψ.residue = 1)
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIc : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (hJc : IsCoprime J (rationalModulusIdeal (𝓞 K) N))
    (hclass : ClassGroup.mk K (integralIdealFractionalUnit I hI) =
      ClassGroup.mk K (integralIdealFractionalUnit J hJ)) :
    ψ.idealHom (integralIdealFractionalUnit I hI) =
      ψ.idealHom (integralIdealFractionalUnit J hJ) := by
  let c := ClassGroup.mk K (integralIdealFractionalUnit I hI)
  let L := (classIdeal K N c⁻¹).val
  have hL : L ≠ ⊥ := classIdeal_ne_bot c⁻¹
  have hcL : IsCoprime L (rationalModulusIdeal (𝓞 K) N) := classIdeal_coprime c⁻¹
  have hlclass : ClassGroup.mk K (integralIdealFractionalUnit L hL) = c⁻¹ :=
    classIdeal_class c⁻¹
  have HI := ψ.coprime_inverse_product hψ L I hL hI hcL hIc (by
    rw [hlclass, inv_inv])
  have HJ := ψ.coprime_inverse_product hψ L J hL hJ hcL hJc (by
    rw [hlclass, inv_inv]
    exact hclass.symm)
  exact mul_left_cancel (HI.trans HJ.symm)

 

def classValue (c : ClassGroup (𝓞 K)) : ℂˣ :=
  ψ.idealHom (integralIdealFractionalUnit (classIdeal K N c).val (classIdeal_ne_bot c))

lemma idealHom_eq_classValue (hψ : ψ.residue = 1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hc : IsCoprime I (rationalModulusIdeal (𝓞 K) N)) :
    ψ.idealHom (integralIdealFractionalUnit I hI) =
      ψ.classValue (ClassGroup.mk K (integralIdealFractionalUnit I hI)) := by
  apply ψ.idealHom_eq_of_coprime_class hψ I _ hI _ hc (classIdeal_coprime _)
  exact (classIdeal_class _).symm

lemma classValue_one (hψ : ψ.residue = 1) : ψ.classValue 1 = 1 := by
  have hc : IsCoprime (⊤ : Ideal (𝓞 K)) (rationalModulusIdeal (𝓞 K) N) := by
    rw [← Ideal.one_eq_top]
    exact isCoprime_one_left
  have H := ψ.idealHom_eq_classValue hψ ⊤ top_ne_bot hc
  simpa only [integralIdealFractionalUnit_top, map_one] using H.symm

lemma classValue_mul (hψ : ψ.residue = 1) (c e : ClassGroup (𝓞 K)) :
    ψ.classValue (c*e) = ψ.classValue c * ψ.classValue e := by
  let I := (classIdeal K N c).val
  let J := (classIdeal K N e).val
  have hI : I ≠ ⊥ := classIdeal_ne_bot c
  have hJ : J ≠ ⊥ := classIdeal_ne_bot e
  have hc : IsCoprime (I*J) (rationalModulusIdeal (𝓞 K) N) :=
    IsCoprime.mul_left_iff.mpr ⟨classIdeal_coprime c, classIdeal_coprime e⟩
  have H := ψ.idealHom_eq_classValue hψ (I*J) (mul_ne_zero hI hJ) hc
  rw [integralUnit_mul I J hI hJ, map_mul, map_mul] at H
  have HI : ClassGroup.mk K (integralIdealFractionalUnit I hI) = c := classIdeal_class c
  have HJ : ClassGroup.mk K (integralIdealFractionalUnit J hJ) = e := classIdeal_class e
  rw [HI, HJ] at H
  exact H.symm

 
def classCharacter (hψ : ψ.residue = 1) : ClassGroup (𝓞 K) →* ℂ where
  toFun c := (ψ.classValue c : ℂ)
  map_one' := by rw [ψ.classValue_one hψ]; rfl
  map_mul' c e := by rw [ψ.classValue_mul hψ]; rfl

lemma allCoefficient_of_residue_one (hψ : ψ.residue = 1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ψ.allCoefficient I = if IsCoprime I (rationalModulusIdeal (𝓞 K) N) then
      ψ.classCharacter hψ (ClassGroup.mk K (integralIdealFractionalUnit I hI)) else 0 := by
  rw [allCoefficient, dite_eq_left hI]
  split_ifs with hc
  · exact congrArg (fun u : ℂˣ => (u:ℂ)) (ψ.idealHom_eq_classValue hψ I hI hc)
  · rfl

 
def classUnitCharacter (hψ : ψ.residue = 1) : ClassGroup (𝓞 K) →* ℂˣ where
  toFun := ψ.classValue
  map_one' := ψ.classValue_one hψ
  map_mul' := ψ.classValue_mul hψ

end EvenRayCharacter

variable {K : Type*} [Field K] [NumberField K]

 

def classRayCharacter (χ : ClassGroup (𝓞 K) →* ℂˣ) : EvenRayCharacter K 1 where
  idealHom := χ.comp (ClassGroup.mk K)
  finiteOrder := ⟨Fintype.card (ClassGroup (𝓞 K)), Fintype.card_pos, fun J => by
    rw [MonoidHom.comp_apply, ← map_pow, pow_card_eq_one, map_one]⟩
  residue := 1
  principalLaw := by
    intro a ha hc
    rw [MulChar.one_apply ((quotient_isUnit_iff_span_coprime _ a).mpr hc)]
    have hspan : Ideal.span {a} ≠ ⊥ := by simpa using ha
    suffices H : ClassGroup.mk K (integralIdealFractionalUnit (Ideal.span {a}) hspan) = 1 by
      simp only [MonoidHom.comp_apply, H, map_one, Units.val_one]
    rw [← map_one (ClassGroup.mk K)]
    symm
    apply (fractionalIdeal_same_class _ _).mpr
    refine ⟨(a : K), (by exact_mod_cast ha), ?_⟩
    simp only [Units.val_one, mul_one]
    change FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) =
      (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K)
    rw [FractionalIdeal.coeIdeal_span_singleton]

namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)

omit [NumberField K] in
lemma coprime_modulus_one (I : Ideal (𝓞 K)) :
    IsCoprime I (rationalModulusIdeal (𝓞 K) 1) := by
  simp only [rationalModulusIdeal, Nat.cast_one, Ideal.span_singleton_one,
    ← Ideal.one_eq_top]
  exact isCoprime_one_right

lemma classRay_coefficient (χ : ClassGroup (𝓞 K) →* ℂˣ)
    (J : integralFractionalIdeals K) :
    (classRayCharacter χ).coefficient J = (χ (ClassGroup.mk K J.val) : ℂ) := by
  simp only [coefficient, coprime_modulus_one, ite_true, classRayCharacter,
    MonoidHom.comp_apply]

lemma classRay_dirichlet (χ : ClassGroup (𝓞 K) →* ℂˣ) (s : ℂ) :
    (classRayCharacter χ).dirichlet s =
      idealClassDirichlet K (fun c => (χ c : ℂ)) s := by
  apply tsum_congr
  intro J
  rw [classRay_coefficient]

lemma coprime_idealOverPrime_iff {p : ℕ} (hp : p.Prime) (P : idealsOverPrime K p) :
    IsCoprime P.val (rationalModulusIdeal (𝓞 K) N) ↔ ¬ p ∣ N := by
  have hd : P.val ∣ Ideal.span {(p : 𝓞 K)} :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp P.property)
  constructor
  · intro hc hdiv
    apply (idealsOverPrime_prime K P.property).not_isUnit
    apply hc.isUnit_of_dvd
    apply dvd_trans hd
    rw [Ideal.dvd_iff_le, rationalModulusIdeal, Ideal.span_singleton_le_iff_mem,
      Ideal.mem_span_singleton]
    exact map_dvd (Nat.castRingHom (𝓞 K)) hdiv
  · intro hn
    apply IsCoprime.of_isCoprime_of_dvd_left _ hd
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hp.coprime_iff_not_dvd.mpr hn).cast

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
