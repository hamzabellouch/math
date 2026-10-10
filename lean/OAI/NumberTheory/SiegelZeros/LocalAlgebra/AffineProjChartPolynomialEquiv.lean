import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Determinants.GenericNormalization
import OAI.NumberTheory.SiegelZeros.Structure.Homogenize

namespace OAI

namespace SiegelZeros

section
namespace WeightedTorusJets.Geometry

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem conePolynomialMap_of_isHomogeneous {K σ : Type*} [CommRing K]
    {f : MvPolynomial (Option σ) K} {n : ℕ} (hf : f.IsHomogeneous n) :
    conePolynomialMap f = Polynomial.C (coneDehomogenize f) * Polynomial.X ^ n := by
  have hv : (fun o : Option σ => Polynomial.C (o.elim (1 : MvPolynomial σ K) X) *
      Polynomial.X) = (fun o : Option σ => o.elim Polynomial.X
        (fun i => Polynomial.C (X i) * Polynomial.X)) := by
    funext o
    cases o <;> simp
  have hc : algebraMap K (Polynomial (MvPolynomial σ K)) =
      Polynomial.C.comp (algebraMap K (MvPolynomial σ K)) := by
    apply RingHom.ext
    intro r
    exact Polynomial.algebraMap_apply (A := MvPolynomial σ K) r
  rw [conePolynomialMap, aeval_def, hc, ← hv,
    homogeneous_eval₂_mul hf, ← MvPolynomial.hom_eval₂]
  rfl

theorem coneAwayEquiv_affineProjChartMap {K σ : Type*} [CommRing K]
    (z : affineProjChart K σ) :
    coneAwayEquiv (algebraMap (affineProjChart K σ)
      (Localization.Away (X (none : Option σ) : MvPolynomial (Option σ) K)) z) =
      algebraMap (Polynomial (MvPolynomial σ K))
        (Localization.Away (Polynomial.X : Polynomial (MvPolynomial σ K)))
          (Polynomial.C (affineProjChartMap (k := K) (fun i : σ => (X i : MvPolynomial σ K)) z)) := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (homogeneousSubmodule (Option σ) K)
    (isHomogeneous_X K (none : Option σ)) z
  let S := MvPolynomial (Option σ) K
  let U := Localization.Away (X (none : Option σ) : S)
  let A := MvPolynomial σ K
  let V := Localization.Away (Polynomial.X : Polynomial A)
  let e : U ≃ₐ[K] V := coneAwayEquiv
  let den : Submonoid.powers (X (none : Option σ) : S) := ⟨X none ^ n, ⟨n, rfl⟩⟩
  have ha' : a.IsHomogeneous n := by
    simpa only [smul_eq_mul, mul_one, mem_homogeneousSubmodule] using ha
  have hunit : IsUnit (algebraMap (Polynomial A) V (Polynomial.X ^ n)) := by
    simpa only [map_pow] using
      (IsLocalization.Away.algebraMap_isUnit (S := V) (Polynomial.X : Polynomial A)).pow n
  have hscale : e (algebraMap S U (den : S)) =
      algebraMap (Polynomial A) V (Polynomial.X ^ n) := by
    change coneAwayEquiv (algebraMap S U (X none ^ n)) = _
    rw [coneAwayEquiv_algebraMap, map_pow, conePolynomialMap_X_none]
  have hraw : (Localization.mk a den : U) * algebraMap S U den = algebraMap S U a := by
    rw [Localization.mk_eq_mk', IsLocalization.mk'_spec]
  have heval : (coneDehomogenize : S →ₐ[K] A) = affineProjEval (k := K)
      (fun i : σ => (X i : A)) := by
    simp only [coneDehomogenize, affineProjEval, ← Option.elim'_eq_elim]
  rw [affineProjChartMap_mk]
  change e (Localization.mk a den) = algebraMap (Polynomial A) V
    (Polynomial.C (affineProjEval (k := K) (fun i : σ => (X i : A)) a))
  apply hunit.mul_right_cancel
  calc
    _ = e (Localization.mk a den) * e (algebraMap S U den) := by rw [hscale]
    _ = e ((Localization.mk a den : U) * algebraMap S U den) := (map_mul e _ _).symm
    _ = e (algebraMap S U a) := congrArg e hraw
    _ = algebraMap (Polynomial A) V (conePolynomialMap a) := coneAwayEquiv_algebraMap a
    _ = _ := by rw [conePolynomialMap_of_isHomogeneous ha', map_mul, heval]

theorem affineProjChartMap_polynomial_injective {K σ : Type*} [CommRing K] :
    Function.Injective (affineProjChartMap (k := K) (fun i : σ => (X i : MvPolynomial σ K))) := by
  intro a b hab
  apply HomogeneousLocalization.val_injective
  apply coneAwayEquiv.injective
  change coneAwayEquiv (algebraMap (affineProjChart K σ) _ a) =
    coneAwayEquiv (algebraMap (affineProjChart K σ) _ b)
  rw [coneAwayEquiv_affineProjChartMap, coneAwayEquiv_affineProjChartMap, hab]

noncomputable def affineProjChartPolynomialEquiv {K σ : Type*} [CommRing K] :
    affineProjChart K σ ≃+* MvPolynomial σ K :=
  RingEquiv.ofBijective (affineProjChartMap (k := K) (fun i : σ => (X i : MvPolynomial σ K)))
    ⟨affineProjChartMap_polynomial_injective,
      affineProjChartMap_surjective _ (by
        intro q
        exact ⟨q, aeval_X_left_apply q⟩)⟩

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI
