import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Hilbert.ConeChartHomogeneousLocal

namespace OAI

namespace SiegelZeros

section
namespace WeightedTorusJets.Geometry

open MvPolynomial HomogeneousLocalization _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra coneIdeal_isPrime

universe uProjEq

noncomputable def normalizedHomogeneousChartEquation {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (n : ℕ) : affineProjChart K σ :=
  Away.mk (homogeneousSubmodule (Option σ) K) (isHomogeneous_X K (none : Option σ))
    (n + f.totalDegree) (X none ^ n * homogenize f) (by
      simpa only [smul_eq_mul, mul_one, mem_homogeneousSubmodule] using
        (isHomogeneous_X_pow (R := K) (none : Option σ) n).mul (homogenize_isHomogeneous f))

theorem affineProjChartMap_normalizedHomogeneousChartEquation {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (n : ℕ) :
    affineProjChartMap (k := K) (fun i : σ => (X i : MvPolynomial σ K))
      (normalizedHomogeneousChartEquation f n) = f := by
  rw [normalizedHomogeneousChartEquation, affineProjChartMap_mk]
  have heval : affineProjEval (k := K) (fun i : σ => (X i : MvPolynomial σ K)) =
      (coneDehomogenize : MvPolynomial (Option σ) K →ₐ[K] MvPolynomial σ K) := by
    simp only [coneDehomogenize, affineProjEval, ← Option.elim'_eq_elim]
  rw [heval, map_mul, map_pow]
  have hX : (coneDehomogenize : MvPolynomial (Option σ) K →ₐ[K] MvPolynomial σ K)
      (X none) = 1 := by simp [coneDehomogenize]
  rw [hX, one_pow, one_mul]
  exact dehomogenize_homogenize f

noncomputable def projectiveStalkPolynomialEquiv {K σ : Type uProjEq} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ((Proj (homogeneousSubmodule (Option σ) K)).presheaf.stalk (coneProjectivePoint p)) ≃+*
      Localization.AtPrime p :=
  (Proj.stalkIso' (homogeneousSubmodule (Option σ) K) (coneProjectivePoint p)).trans
    (projectiveLocalPolynomialEquiv p)

noncomputable def normalizedHomogeneousStalkEquation {K σ : Type uProjEq} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (f : MvPolynomial σ K) (n : ℕ) :
    (Proj (homogeneousSubmodule (Option σ) K)).presheaf.stalk (coneProjectivePoint p) :=
  (Proj.stalkIso' (homogeneousSubmodule (Option σ) K) (coneProjectivePoint p)).symm
    (coneChartToHomogeneousLocal p (normalizedHomogeneousChartEquation f n))

theorem projectiveStalkPolynomialEquiv_normalizedEquation {K σ : Type uProjEq} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (f : MvPolynomial σ K) (n : ℕ) :
    projectiveStalkPolynomialEquiv p (normalizedHomogeneousStalkEquation p f n) =
      algebraMap (MvPolynomial σ K) (Localization.AtPrime p) f := by
  have h := congrArg (projectiveLocalPolynomialEquiv p)
    ((Proj.stalkIso' (homogeneousSubmodule (Option σ) K) (coneProjectivePoint p)).apply_symm_apply
      (coneChartToHomogeneousLocal p (normalizedHomogeneousChartEquation f n)))
  exact h.trans ((projectiveLocalPolynomialEquiv_chart p _).trans
    (congrArg (algebraMap (MvPolynomial σ K) (Localization.AtPrime p))
      (affineProjChartMap_normalizedHomogeneousChartEquation f n)))

theorem projectiveStalk_normalized_parameter_ideal {ι : Type*} {K σ : Type uProjEq} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (f : ι → MvPolynomial σ K) (n : ι → ℕ) :
    (Ideal.span (Set.range fun i => normalizedHomogeneousStalkEquation p (f i) (n i))).map
      (projectiveStalkPolynomialEquiv p).toRingHom =
        (Ideal.span (Set.range f)).map (algebraMap (MvPolynomial σ K) (Localization.AtPrime p)) := by
  simp only [Ideal.map_span, ← Set.range_comp, Function.comp_def]
  exact congrArg (fun g : ι → Localization.AtPrime p => Ideal.span (Set.range g))
    (funext fun i => projectiveStalkPolynomialEquiv_normalizedEquation p (f i) (n i))

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI
