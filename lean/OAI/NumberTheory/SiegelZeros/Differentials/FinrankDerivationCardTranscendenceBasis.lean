import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.CoordinateLocalizedPrime
import OAI.NumberTheory.SiegelZeros.Structure.LinearShearHom

namespace OAI

namespace SiegelZeros


open Module
open scoped RatFunc

namespace WeightedTorusJets.Geometry

theorem finrank_derivation_eq_card_transcendenceBasis {K F ι : Type*}
    [Field K] [CharZero K] [Field F] [Algebra K F] [Fintype ι]
    (v : ι → F) (hv : IsTranscendenceBasis K v) :
    finrank F (Derivation K F F) = Fintype.card ι := by
  classical
  let P := MvPolynomial ι K
  let : Algebra P F := (MvPolynomial.aeval v).toRingHom.toAlgebra
  have : IsScalarTower K P F := IsScalarTower.of_algHom (MvPolynomial.aeval v)
  have : FaithfulSMul P F :=
    (faithfulSMul_iff_algebraMap_injective P F).mpr hv.1
  have : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range v)) F := hv.isAlgebraic
  have : Algebra.IsAlgebraic P F :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq hv.1.aevalEquiv (RingHom.id F)
      hv.1.aevalEquiv.surjective Function.injective_id (by
        apply RingHom.ext
        intro p
        exact hv.1.algebraMap_aevalEquiv p)
  let E := FractionRing P
  let := FractionRing.liftAlgebra P F
  have : Algebra.IsAlgebraic E F := IsFractionRing.comap_isAlgebraic_iff.mp ‹_›
  have : Algebra.FormallyEtale E F := Algebra.FormallyEtale.of_isSeparable E F
  have : Algebra.FormallyEtale P E :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  have : Algebra.FormallyEtale P F := Algebra.FormallyEtale.comp P E F
  let b : Basis ι F Ω[F⁄K] := ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K P F)
  exact finrank_eq_card_basis
    (b.dualBasis.map (KaehlerDifferential.linearMapEquivDerivation K F (M := F)))

theorem finrank_derivation_eq_trdeg_toENat {K F : Type*}
    [Field K] [CharZero K] [Field F] [Algebra K F]
    (hfin : Algebra.trdeg K F < Cardinal.aleph0) :
    (finrank F (Derivation K F F) : ℕ∞) = (Algebra.trdeg K F).toENat := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K F
  have : Finite s := Cardinal.lt_aleph0_iff_finite.mp
    (hs.cardinalMk_eq_trdeg.trans_lt hfin)
  let := Fintype.ofFinite s
  rw [finrank_derivation_eq_card_transcendenceBasis _ hs, ← hs.cardinalMk_eq_trdeg]
  simp

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

theorem finiteType_dimension_trdeg {K A : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) ∧ Algebra.trdeg K A = n := by
  obtain ⟨n, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral (MvPolynomial (Fin n) K) A := ⟨hint⟩
  let : FaithfulSMul (MvPolynomial (Fin n) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine ⟨n, ?_, ?_⟩
  · rw [Geometry.ringKrullDim_eq_of_integral_faithful_goingDown
      (R := MvPolynomial (Fin n) K)]
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
  · have hz : Algebra.trdeg (MvPolynomial (Fin n) K) A = 0 :=
      trdeg_eq_zero_iff.mpr inferInstance
    have h := lift_trdeg_add_eq K (MvPolynomial (Fin n) K) A
    simpa [hz, MvPolynomial.trdeg_of_isDomain] using h.symm

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

theorem ringKrullDim_eq_finrank_derivation {K A F : Type*}
    [Field K] [CharZero K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] [Field F] [Algebra K F] [Algebra A F]
    [IsScalarTower K A F] [IsFractionRing A F] :
    ringKrullDim A = (finrank F (Derivation K F F) : WithBot ℕ∞) := by
  obtain ⟨n, hdim, htrdeg⟩ := WeightedTorusJets.finiteType_dimension_trdeg
    (K := K) (A := A)
  let : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F (nonZeroDivisors A)
  have hz : Algebra.trdeg A F = 0 := trdeg_eq_zero_iff.mpr inferInstance
  have hF : Algebra.trdeg K F = n := by
    simpa [htrdeg, hz] using (lift_trdeg_add_eq K A F).symm
  have hfin : Algebra.trdeg K F < Cardinal.aleph0 := by
    rw [hF]
    exact Cardinal.natCast_lt_aleph0
  have hder : finrank F (Derivation K F F) = n := by
    simpa [hF] using finrank_derivation_eq_trdeg_toENat hfin
  rw [hder]
  exact hdim



theorem comap_aeval_eq_bot_of_independent_quotient
    {K R σ : Type*} [Field K] [CommRing R] [Algebra K R]
    (I : Ideal R) (x : σ → R)
    (hx : AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (x i))) :
    I.comap (MvPolynomial.aeval (R := K) x).toRingHom = ⊥ := by
  apply bot_unique
  intro p hp
  apply hx.eq_zero_of_aeval_eq_zero p
  have he := MvPolynomial.comp_aeval_apply (f := x) (φ := Ideal.Quotient.mkₐ K I) (p := p)
  simp only [Ideal.Quotient.mkₐ_eq_mk] at he
  rw [← he]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hp

end WeightedTorusJets.Geometry


noncomputable section
open scoped BigOperators
open MvPolynomial

namespace WeightedTorusJets.Geometry

theorem coordinateSplit_height
    {K σ : Type*} [CommRing K] (s : Set σ) (p : Ideal (MvPolynomial σ K)) :
    (p.comap (coordinateSplit s).symm.toRingHom).height = p.height :=
  by
    exact RingEquiv.height_comap (coordinateSplit (K := K) s).symm.toRingEquiv p

attribute [local instance] MvPolynomial.algebraMvPolynomial in

theorem coordinateSplit_localized_mem_minimalPrimes
    {K σ : Type*} [Field K] (s : Set σ) (I p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (hp : p ∈ I.minimalPrimes)
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (X i)))) :
    ((p.comap (coordinateSplit s).symm.toRingHom).map
      (MvPolynomial.map (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K))))) ∈
    ((I.comap (coordinateSplit s).symm.toRingHom).map
      (MvPolynomial.map (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K))))).minimalPrimes := by
  let B := MvPolynomial s K
  let F := FractionRing B
  let A := MvPolynomial (sᶜ : Set σ) B
  let A' := MvPolynomial (sᶜ : Set σ) F
  let p' : Ideal A := p.comap (coordinateSplit s).symm.toRingHom
  let I' : Ideal A := I.comap (coordinateSplit s).symm.toRingHom
  let M : Submonoid A := (nonZeroDivisors B).map MvPolynomial.C
  have hp' : p' ∈ I'.minimalPrimes :=
    Ideal.minimalPrimes_comap_of_surjective (coordinateSplit (K := K) s).symm.surjective hp
  have hcoeff : p'.comap MvPolynomial.C = ⊥ :=
    coordinateSplit_comap_coefficients_eq_bot_of_fractionField s p hs
  have hdisj : Disjoint (M : Set A) (p' : Set A) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨b, hb, rfl⟩ hbp
    have hz : b = 0 := by
      have hmem : b ∈ p'.comap MvPolynomial.C := hbp
      simpa [hcoeff] using hmem
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hb) hz
  change p'.map (algebraMap A A') ∈ (I'.map (algebraMap A A')).minimalPrimes
  rw [IsLocalization.minimalPrimes_map M]
  change (p'.map (algebraMap A A')).under A ∈ I'.minimalPrimes
  rw [IsLocalization.under_map_of_isPrime_disjoint M A' (show p'.IsPrime from inferInstance) hdisj]
  exact hp'

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

theorem mvPolynomial_height_eq_card_iff_isMaximal {σ : Type*} [Fintype σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    p.height = Fintype.card σ ↔ p.IsMaximal := by
  constructor
  · intro hp
    have : FiniteRingKrullDim (MvPolynomial σ K) := by
      refine finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨by simp, ?_⟩
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
        ringKrullDim_eq_zero_of_field, zero_add]
      intro htop
      exact ENat.natCast_ne_top (Nat.card σ) (WithBot.coe_injective htop)
    apply Ideal.isMaximal_of_height_eq_ringKrullDim
    simp [hp]
  · intro hp
    have := hp
    exact maximal_mvPolynomial_height p

end WeightedTorusJets.Geometry


namespace WeightedTorusJets.Geometry

open scoped AlgebraMonoidAlgebra

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coordinateLocalizedPrime_isPrime {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (MvPolynomial.X i)))) :
    (coordinateLocalizedPrime s p).IsPrime := by
  exact (coefficient_localization_prime_height (F := FractionRing (MvPolynomial s K))
    (p.comap (coordinateSplit (K := K) s).symm.toRingHom)
    (coordinateSplit_comap_coefficients_eq_bot_of_fractionField s p hs)).1

end WeightedTorusJets.Geometry
namespace WeightedTorusJets

theorem trdeg_eq_of_integral_polynomial_base {K A : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] (n : ℕ)
    (g : MvPolynomial (Fin n) K →ₐ[K] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral) :
    Algebra.trdeg K A = n := by
  let : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral (MvPolynomial (Fin n) K) A := ⟨hint⟩
  let : FaithfulSMul (MvPolynomial (Fin n) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hz : Algebra.trdeg (MvPolynomial (Fin n) K) A = 0 :=
    trdeg_eq_zero
  have h := lift_trdeg_add_eq K (MvPolynomial (Fin n) K) A
  simpa [hz, MvPolynomial.trdeg_of_isDomain] using h.symm

theorem fractionField_trdeg_eq_nat {K A F : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Field F]
    [Algebra K F] [Algebra A F] [IsScalarTower K A F] [IsFractionRing A F]
    (n : ℕ) (h : Algebra.trdeg K A = n) : Algebra.trdeg K F = n := by
  let : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F (nonZeroDivisors A)
  have hz : Algebra.trdeg A F = 0 := trdeg_eq_zero
  have htower := lift_trdeg_add_eq K A F
  simpa [h, hz] using htower.symm

end WeightedTorusJets
namespace WeightedTorusJets.Geometry

theorem polynomial_prime_height_add_quotient_dim_of_finite
    {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ K ⧸ p) = Nat.card σ := by
  obtain ⟨t, ht, hmax, _, hheight, _⟩ := exists_coordinate_localization p
  obtain ⟨d, hdim, htr⟩ := WeightedTorusJets.finiteType_dimension_trdeg
    (K := K) (A := MvPolynomial σ K ⧸ p)
  have hF : Algebra.trdeg K (FractionRing (MvPolynomial σ K ⧸ p)) = d :=
    WeightedTorusJets.fractionField_trdeg_eq_nat d htr
  have hcard : Nat.card t = d := by
    have h := congrArg Cardinal.toNat ht.lift_cardinalMk_eq_trdeg
    simpa [Nat.card, hF] using h
  rw [← hheight, hdim, ← hcard]
  have hsum : Nat.card (tᶜ : Set σ) + Nat.card t = Nat.card σ := by
    simpa only [Nat.card_coe_set_eq] using Set.ncard_compl_add_ncard t
  exact_mod_cast hsum



variable {K σ : Type*} [Field K] [Finite σ]

theorem polynomial_normalization_quotient_dimension_finite {s : ℕ}
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial σ K ⧸ p)
    (hg : Function.Injective g) (hgi : g.IsIntegral) :
    ringKrullDim (MvPolynomial σ K ⧸ p) = (s : WithBot ℕ∞) := by
  obtain ⟨d, hdim, htr⟩ := WeightedTorusJets.finiteType_dimension_trdeg
    (K := K) (A := MvPolynomial σ K ⧸ p)
  have hs := WeightedTorusJets.trdeg_eq_of_integral_polynomial_base s g hg hgi
  have hd : d = s := by exact_mod_cast htr.symm.trans hs
  simpa only [hd] using hdim

theorem polynomial_normalization_count_add_height_finite {s : ℕ}
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial σ K ⧸ p)
    (hg : Function.Injective g) (hgi : g.IsIntegral) :
    (s : ℕ∞) + p.height = Nat.card σ := by
  have h := polynomial_prime_height_add_quotient_dim_of_finite (K := K) p
  rw [polynomial_normalization_quotient_dimension_finite p g hg hgi] at h
  have hh : p.height + (s : ℕ∞) = Nat.card σ := by exact_mod_cast h
  simpa only [add_comm] using hh

theorem polynomial_normalization_count_le_finite {s : ℕ}
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial σ K ⧸ p)
    (hg : Function.Injective g) (hgi : g.IsIntegral) : s ≤ Nat.card σ := by
  have h := polynomial_normalization_count_add_height_finite p g hg hgi
  have hs : (s : ℕ∞) ≤ Nat.card σ := by rw [← h]; exact le_self_add
  exact_mod_cast hs

theorem polynomial_normalization_height_eq_sub_finite {s : ℕ}
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial σ K ⧸ p)
    (hg : Function.Injective g) (hgi : g.IsIntegral) : p.height = (Nat.card σ - s : ℕ) := by
  have h := polynomial_normalization_count_add_height_finite p g hg hgi
  have hs := polynomial_normalization_count_le_finite p g hg hgi
  have hn : (Nat.card σ : ℕ∞) = (s : ℕ∞) + ((Nat.card σ - s : ℕ) : ℕ∞) := by
    rw [← Nat.cast_add, Nat.add_sub_of_le hs]
  rw [hn] at h
  exact ENat.add_right_injective_of_ne_top (by simp : (s : ℕ∞) ≠ ⊤) h

end WeightedTorusJets.Geometry


end


end SiegelZeros

end OAI
