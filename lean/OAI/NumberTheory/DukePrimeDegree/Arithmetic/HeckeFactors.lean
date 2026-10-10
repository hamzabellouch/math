import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ArtinOrders
import OAI.NumberTheory.PrimePackets.RayRealization
import OAI.NumberTheory.PrimePackets.CosetMeromorphic

namespace OAI

/-!
# The principal cyclic Hecke factor

The principal factor in a cyclic Artin factorization is the actual
Dedekind zeta function with the finitely many Euler factors at the chosen
modulus removed. A nonprincipal factor is the proved entire continuation
of its realized even ray character.
-/

noncomputable section

open Filter Set Module
open scoped NumberField nonZeroDivisors BigOperators Classical

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

lemma principal_artin_coefficient (N : ℕ) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (hc : IsCoprime I (ThetaConstruction.rationalModulusIdeal (𝓞 F) N)) :
    artinCoefficient F E 1 N I = 1 := by
  simp [artinCoefficient, hI, hc, GaloisIdealCharacter.idealHom]

/-- The principal Artin Dirichlet series agrees with the incomplete
Dedekind zeta function in the half-plane of absolute convergence. -/
theorem principal_artinDirichlet_eq (N : ℕ) (hN : 0 < N)
    {s : ℂ} (hs : 1 < s.re) :
    artinDirichlet F E 1 N s =
      NumberField.dedekindZeta F s * removedEulerPolynomial F N s := by
  let C : Nat.Primes → ℂ := fun p =>
    if p ∈ badRationalPrimes N then
      ∏ P : idealsOverPrime F p.val, (1 - (Ideal.absNorm P.val : ℂ)^(-s)) else 1
  have hC : HasProd C (removedEulerPolynomial F N s) := by
    have h : HasProd C (∏ p ∈ badRationalPrimes N, C p) :=
      hasProd_prod_of_ne_finset_one (s := badRationalPrimes N) (f := C)
        (fun p hp => ite_eq_right hp)
    simpa only [C, Finset.prod_ite_mem, Finset.inter_self, removedEulerPolynomial] using h
  apply (ArtinSeries.dirichlet_hasProd (F := F) (E := E) 1 N hs).unique
  apply ((dedekindZeta_hasProd F hs).mul hC).congr_fun
  intro p
  have hpN : p ∈ badRationalPrimes N ↔ p.val ∣ N := by
    change (⟨p.val, p.property⟩ : Subtype Nat.Prime) ∈
      N.primeFactors.subtype Nat.Prime ↔ _
    rw [Finset.mem_subtype, Nat.mem_primeFactors]
    exact ⟨fun h => h.2.1, fun h => ⟨p.property, h, hN.ne'⟩⟩
  by_cases hp : p.val ∣ N
  · rw [ArtinSeries.local_euler_bad F E 1 p hp hs]
    simp only [C, ite_eq_left (hpN.mpr hp)]
    unfold primeIdealEulerFactor
    rw [← Finset.prod_mul_distrib]
    simp only [inv_mul_cancel₀ (primeEuler_denominator_ne_zero F _
      (zero_lt_one.trans hs)), Finset.prod_const_one]
  · simp only [C, ite_eq_right (mt hpN.mp hp), mul_one]
    unfold primeIdealEulerFactor
    apply Finset.prod_congr rfl
    intro P _
    have hP := (mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property
    have hP0 : P.val ≠ ⊥ := by
      intro he
      rw [he, Ideal.mem_bot] at hP
      exact p.property.ne_zero (Nat.cast_eq_zero.mp hP.2)
    have hc : IsCoprime P.val (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) := by
      apply Ideal.isCoprime_iff_codisjoint.mpr
      apply Codisjoint.mono ((Ideal.span_singleton_le_iff_mem _).mpr hP.2) le_rfl
      exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr
        (p.property.coprime_iff_not_dvd.mpr hp).cast).codisjoint
    rw [ArtinSeries.idealTerm_apply]
    change (1 - artinCoefficient F E 1 N P.val * _)⁻¹ = (1 - _)⁻¹
    rw [principal_artin_coefficient F E N P.val hP0 hc, one_mul]

theorem principal_continuation_eq_artinDirichlet
    [NumberField.IsTotallyReal F] {d : ℕ}
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (N : ℕ) (hN : 0 < N) {s : ℂ} (hs : 1 < s.re) :
    cosetMeromorphic σ hn N s = artinDirichlet F E 1 N s := by
  rw [cosetMeromorphic_eq_dedekindZeta σ hn N hs,
    principal_artinDirichlet_eq F E N hN hs]

/-- The entire continuation attached to a realized nonprincipal ray
character agrees with the actual Frobenius Artin Dirichlet series. -/
theorem nonprincipal_continuation_eq_artinDirichlet
    [NumberField.IsTotallyReal F] {d N : ℕ} [NeZero N]
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (χ : (E ≃ₐ[F] E) →* ℂˣ) (ψ : EvenRayCharacter F N)
    (hid : ψ.idealHom = idealHom F E χ) (hψ : ψ.IsNonprincipal)
    {s : ℂ} (hs : 1 < s.re) :
    ψ.nonprincipalContinued σ hn s = artinDirichlet F E χ N s := by
  rw [ψ.nonprincipalContinued_eq_dirichlet σ hn hψ hs,
    ψ.dirichlet_eq_ideal_tsum hs]
  apply tsum_congr
  intro I
  rw [EvenRayCharacter.idealTerm_apply]
  simp only [EvenRayCharacter.allCoefficient, artinCoefficient, hid]

/-- The conductor kernel gives one common family of even ray
realizations for all cyclic characters. -/
theorem exists_cyclic_ray_family
    [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
    [IsCyclic (E ≃ₐ[F] E)] (N : ℕ) (hN : 0 < N)
    (hk : ∀ χ : (E ≃ₐ[F] E) →* ℂˣ,
      PrincipalRay.KernelLaw (idealHom F E χ) N) :
    ∃ ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N,
      (∀ χ, (ψ χ).idealHom = idealHom F E χ) ∧
      ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal := by
  let ψ := fun χ : (E ≃ₐ[F] E) →* ℂˣ =>
    PrincipalRay.realize (idealHom F E χ) N hN (hk χ) (idealHom_finiteOrder F E χ)
  refine ⟨ψ, fun _ => rfl, ?_⟩
  intro χ hχ
  obtain ⟨P, hc, hP⟩ := Unfinished.actual_frobenius_nonprincipal F E χ hχ N hN
  refine ⟨P.asIdeal, P.ne_bot, hc, ?_⟩
  change idealHom F E χ (integralIdealFractionalUnit P.asIdeal P.ne_bot) ≠ 1
  rwa [idealHom_prime]

end DukePrimeDegree

end

end OAI
