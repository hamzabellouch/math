import Mathlib
import OAI.NumberTheory.PrimePackets.FrobeniusNonprincipal

namespace OAI

noncomputable section
open Module
open scoped NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets.PrincipalRay
open ThetaConstruction
variable {F : Type*} [Field F] [NumberField F]
variable (φ : (FractionalIdeal (𝓞 F)⁰ F)ˣ →* ℂˣ)

def principalValue (a : 𝓞 F) (ha : a ≠ 0) : ℂˣ :=
  φ (integralIdealFractionalUnit (Ideal.span {a})
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha))

lemma principalValue_mul (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0) :
    principalValue φ (a*b) (mul_ne_zero ha hb) =
      principalValue φ a ha * principalValue φ b hb := by
  have haI : Ideal.span {a} ≠ (⊥ : Ideal (𝓞 F)) := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha
  have hbI : Ideal.span {b} ≠ (⊥ : Ideal (𝓞 F)) := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hb
  have h := EvenRayCharacter.integralUnit_mul (Ideal.span {a}) (Ideal.span {b}) haI hbI
  simp only [Ideal.span_singleton_mul_span_singleton] at h
  exact (congrArg φ h).trans (map_mul φ _ _)

lemma exists_nonzero_lift (N : ℕ) (hN : 0 < N)
    (x : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) a = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  by_cases ha : a = 0
  · subst a
    refine ⟨(N : 𝓞 F), Nat.cast_ne_zero.mpr hN.ne', ?_⟩
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  · exact ⟨a, ha, rfl⟩

def residueLift (N : ℕ) (hN : 0 < N)
    (u : ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ) : 𝓞 F :=
  Classical.choose (exists_nonzero_lift N hN (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N))

lemma residueLift_ne_zero (N : ℕ) (hN : 0 < N)
    (u : ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ) : residueLift N hN u ≠ 0 :=
  (Classical.choose_spec (exists_nonzero_lift N hN (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N))).1

lemma residueLift_spec (N : ℕ) (hN : 0 < N)
    (u : ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ) :
    Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) (residueLift N hN u) = (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N) :=
  (Classical.choose_spec (exists_nonzero_lift N hN (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N))).2

def KernelLaw (N : ℕ) : Prop := ∀ (a : 𝓞 F) (ha : a ≠ 0),
  a - 1 ∈ rationalModulusIdeal (𝓞 F) N → principalValue φ a ha = 1

lemma principalValue_eq (N : ℕ) (hN : 0 < N) (hk : KernelLaw φ N)
    (u : ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ)
    (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hqA : Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) a = (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N))
    (hqB : Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) b = (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)) :
    principalValue φ a ha = principalValue φ b hb := by
  let c := residueLift N hN u⁻¹
  have hc : c ≠ 0 := residueLift_ne_zero N hN u⁻¹
  have hqc : Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) c = (u⁻¹ : ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ) :=
    residueLift_spec N hN u⁻¹
  have hac : a*c - 1 ∈ rationalModulusIdeal (𝓞 F) N := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, hqA, hqc, map_one, Units.mul_inv, sub_self]
  have hbc : b*c - 1 ∈ rationalModulusIdeal (𝓞 F) N := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, hqB, hqc, map_one, Units.mul_inv, sub_self]
  have hA := hk (a*c) (mul_ne_zero ha hc) hac
  have hB := hk (b*c) (mul_ne_zero hb hc) hbc
  rw [principalValue_mul φ a c ha hc] at hA
  rw [principalValue_mul φ b c hb hc] at hB
  exact mul_right_cancel (hA.trans hB.symm)

def residueHom (N : ℕ) (hN : 0 < N) (hk : KernelLaw φ N) :
    ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ →* ℂˣ where
  toFun u := principalValue φ (residueLift N hN u) (residueLift_ne_zero N hN u)
  map_one' := by
    apply hk
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_one, residueLift_spec, Units.val_one, sub_self]
  map_mul' u v := by
    rw [← principalValue_mul]
    apply principalValue_eq φ N hN hk (u*v)
    · exact residueLift_spec N hN (u*v)
    · rw [map_mul, residueLift_spec, residueLift_spec, Units.val_mul]

lemma residueHom_spec (N : ℕ) (hN : 0 < N) (hk : KernelLaw φ N)
    (a : 𝓞 F) (ha : a ≠ 0)
    (u : ((𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)ˣ)
    (hq : Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) a = (u : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N)) :
    residueHom φ N hN hk u = principalValue φ a ha :=
  principalValue_eq φ N hN hk u _ a (residueLift_ne_zero N hN u) ha
    (residueLift_spec N hN u) hq

def realize (N : ℕ) (hN : 0 < N) (hk : KernelLaw φ N)
    (hf : ∃ e : ℕ, 0 < e ∧ ∀ J, φ J ^ e = 1) : EvenRayCharacter F N where
  idealHom := φ
  finiteOrder := hf
  residue := MulChar.ofUnitHom (residueHom φ N hN hk)
  principalLaw a ha hc := by
    have hu := (quotient_isUnit_iff_span_coprime (rationalModulusIdeal (𝓞 F) N) a).mpr hc
    change (principalValue φ a ha : ℂ) = _
    rw [show Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) a = (hu.unit : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N) from hu.unit_spec.symm,
      MulChar.ofUnitHom_coe, residueHom_spec φ N hN hk a ha hu.unit hu.unit_spec.symm]

lemma kernel_of_realization (N : ℕ) (ψ : EvenRayCharacter F N)
    (he : ψ.idealHom = φ) : KernelLaw φ N := by
  intro a ha hc
  have hq : Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) a = 1 := by
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hc
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  have hcop : IsCoprime (Ideal.span {a}) (rationalModulusIdeal (𝓞 F) N) := by
    apply (quotient_isUnit_iff_span_coprime _ a).mp
    rw [hq]
    exact isUnit_one
  apply Units.ext
  have h := ψ.principalLaw a ha hcop
  rw [he, hq, map_one] at h
  exact h

end PrimeDegreePackets.PrincipalRay
end

noncomputable section
open Module
open scoped NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets.GaloisIdealCharacter
 

theorem actual_ray_realization_iff
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [IsCyclic (E ≃ₐ[F] E)]
    (χ : (E ≃ₐ[F] E) →* ℂˣ) (hχ : χ ≠ 1) (N : ℕ) (hN : 0 < N) :
    (∃ ψ : EvenRayCharacter F N,
      ψ.idealHom = idealHom F E χ ∧ ψ.IsNonprincipal) ↔
    (∀ (a : 𝓞 F) (ha : a ≠ 0),
      a - 1 ∈ ThetaConstruction.rationalModulusIdeal (𝓞 F) N →
      idealHom F E χ (integralIdealFractionalUnit (Ideal.span {a})
        (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha)) = 1) := by
  constructor
  · rintro ⟨ψ, he, _⟩
    exact PrincipalRay.kernel_of_realization _ N ψ he
  · intro hk
    let ψ := PrincipalRay.realize (idealHom F E χ) N hN hk (idealHom_finiteOrder F E χ)
    refine ⟨ψ, rfl, ?_⟩
    obtain ⟨P, hc, hP⟩ := Unfinished.actual_frobenius_nonprincipal F E χ hχ N hN
    refine ⟨P.asIdeal, P.ne_bot, hc, ?_⟩
    change idealHom F E χ (integralIdealFractionalUnit P.asIdeal P.ne_bot) ≠ 1
    rwa [idealHom_prime]
end PrimeDegreePackets.GaloisIdealCharacter
end

end OAI
