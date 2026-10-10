import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

theorem prime_quotientMul_injective (P : Ideal A) [P.IsPrime]
    (x : A) (hx : x ∉ P) : Function.Injective (quotientMul P x) := by
  have hx0 : Ideal.Quotient.mk P x ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hx
  intro y z hyz
  change x • y = x • z at hyz
  simp only [Algebra.smul_def] at hyz
  exact mul_left_cancel₀ hx0 hyz

theorem prime_colon_length_zero (P : Ideal A) [P.IsPrime]
    (x : A) (hx : x ∉ P) :
    Module.length A ((P.colon {x}) ⧸ P.submoduleOf (P.colon {x})) = 0 :=
  regular_colon_length_zero P x (prime_quotientMul_injective P x hx)

theorem quotientMul_eq_zero_of_mem (P : Ideal A) (x : A) (hx : x ∈ P) :
    quotientMul P x = 0 := by
  apply LinearMap.ext
  intro y
  obtain ⟨a, rfl⟩ := P.mkQ_surjective y
  change quotientMul P x (P.mkQ a) = 0
  rw [quotientMul_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact P.mul_mem_left a hx

noncomputable def minimalPrimeCutSum [IsNoetherianRing A]
    (I : Ideal A) (x : A) : ℕ∞ := by
  classical
  letI : Fintype I.minimalPrimes :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).fintype
  exact ∑ P : I.minimalPrimes,
    letI : P.val.IsPrime := P.property.1.1
    Module.length (Localization.AtPrime P.val)
      (Localization.AtPrime P.val ⧸
        I.map (algebraMap A (Localization.AtPrime P.val))) *
      Module.length A (A ⧸ (P.val ⊔ Ideal.span {x}))

def LocalOneCutLengthStatement (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] : Prop :=
  ∀ (I : Ideal A) (x : A),
    ringKrullDim (A ⧸ I) = 1 →
    Function.Injective (quotientMul I x) →
    (I ⊔ Ideal.span {x}).IsPrimary →
    (I ⊔ Ideal.span {x}).radical = IsLocalRing.maximalIdeal A →
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) = minimalPrimeCutSum I x

end PiExponentJets.W28.LocalIntersection

end OAI
