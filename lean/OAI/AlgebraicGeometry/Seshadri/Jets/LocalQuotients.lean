import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Analytic.CoordinateJets
import OAI.AlgebraicGeometry.Seshadri.Jets.FormalAdic

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial IsLocalRing
open MaximalSeshadri.FormalAdic MaximalSeshadri.LocalComparison
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

lemma formalTaylor_surjective_jet
    (ρ : S →ₐ[F] F) (τ : S →ₐ[F] MvPowerSeries σ F)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + MvPowerSeries.X i)
    (n : ℕ) : Function.Surjective ((formalTrunc n).comp τ) := by
  have heq : ((formalTrunc n).comp τ).comp
      (IsScalarTower.toAlgHom F (MvPolynomial σ F) S) =
      (Ideal.Quotient.mkₐ F _).comp (polynomialTranslate
        (fun i => ρ (algebraMap (MvPolynomial σ F) S (X i)))).toAlgHom := by
    ext i
    change formalTrunc n (τ (algebraMap (MvPolynomial σ F) S (X i))) = _
    rw [hcoord]
    have hpoly := formalTrunc_polynomial n
      (C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + X i)
    simpa [polynomialTranslate, add_comm] using hpoly
  apply Function.Surjective.of_comp (g := IsScalarTower.toAlgHom F (MvPolynomial σ F) S)
  change Function.Surjective (((formalTrunc n).comp τ).comp
    (IsScalarTower.toAlgHom F (MvPolynomial σ F) S))
  rw [heq]
  exact Ideal.Quotient.mk_surjective.comp (polynomialTranslate _).surjective

lemma formalTaylor_surjective_localJet
    (ρ : S →ₐ[F] F) (τ : S →ₐ[F] MvPowerSeries σ F)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + MvPowerSeries.X i)
    (n : ℕ) : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal (MvPowerSeries σ F) ^ n)).comp τ.toRingHom) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨s, hs⟩ := formalTaylor_surjective_jet ρ τ hcoord n (formalTrunc n y)
  refine ⟨s, Ideal.Quotient.eq.mpr ?_⟩
  rw [← trunc_kernel_maximalIdeal, RingHom.mem_ker]
  change formalTrunc n (τ s - y) = 0
  rw [map_sub, sub_eq_zero]
  exact hs

variable [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S]

lemma formalTaylor_localJet_kernel
    (ρ : S →ₐ[F] F) (τ : S →ₐ[F] MvPowerSeries σ F)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + MvPowerSeries.X i)
    (n : ℕ) : RingHom.ker
      ((Ideal.Quotient.mk (maximalIdeal (MvPowerSeries σ F) ^ n)).comp τ.toRingHom) =
      (RingHom.ker ρ) ^ n := by
  by_cases hn : n = 0
  · simp [hn, ← RingHom.comap_ker, Ideal.mk_ker]
  rw [← RingHom.comap_ker, Ideal.mk_ker, ← trunc_kernel_maximalIdeal,
    RingHom.comap_ker]
  exact formalTaylor_detects_ideal_power ρ τ hconst hcoord n (Nat.pos_of_ne_zero hn)

omit [Finite σ] [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]
  [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S] in
lemma formalTaylor_comap_maximalIdeal
    (ρ : S →ₐ[F] F) (τ : S →ₐ[F] MvPowerSeries σ F)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s) :
    (maximalIdeal (MvPowerSeries σ F)).comap τ.toRingHom = RingHom.ker ρ := by
  ext s
  rw [Ideal.mem_comap, maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker, RingHom.mem_ker]
  exact (congrArg (· = 0) (hconst s)).to_iff

variable [IsNoetherianRing S]

def finiteLocalTaylorQuotient
    (ρ : S →ₐ[F] F) (τ : S →ₐ[F] MvPowerSeries σ F)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + MvPowerSeries.X i)
    (A : Type*) [CommRing A] [Algebra S A] [Algebra F A]
    [IsScalarTower F S A] [IsLocalization.AtPrime A (RingHom.ker ρ)]
    [IsLocalRing A] (I : Ideal A)
    [FiniteDimensional F (MvPowerSeries σ F ⧸ I.map
      (localTaylorLift (RingHom.ker ρ) A τ (formalTaylor_comap_maximalIdeal ρ τ hconst)).toRingHom)] :
    (A ⧸ I) ≃ₐ[F] (MvPowerSeries σ F ⧸ I.map
      (localTaylorLift (RingHom.ker ρ) A τ (formalTaylor_comap_maximalIdeal ρ τ hconst)).toRingHom) := by
  let T := localTaylorLift (RingHom.ker ρ) A τ (formalTaylor_comap_maximalIdeal ρ τ hconst)
  have hT : T.toRingHom.comp (algebraMap S A) = τ.toRingHom := localTaylorLift_comp _ _ _ _
  letI : IsNoetherianRing A := IsLocalization.isNoetherianRing (RingHom.ker ρ).primeCompl A inferInstance
  exact finiteQuotientEquiv T
    (fun n => localizedJet_surjective τ.toRingHom T.toRingHom hT _ n
      (formalTaylor_surjective_localJet ρ τ hcoord n))
    (fun n => localizedJet_kernel (RingHom.ker ρ) τ.toRingHom T.toRingHom hT _ n
      (formalTaylor_localJet_kernel ρ τ hconst hcoord n)) I

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
