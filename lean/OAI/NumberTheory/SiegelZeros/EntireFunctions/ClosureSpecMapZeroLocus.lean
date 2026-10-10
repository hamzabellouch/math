import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Intersection.ConeProjectivePoint

namespace OAI

namespace SiegelZeros

section
section TorusProjectiveClosureSource
noncomputable section
open scoped BigOperators

section
namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

attribute [local instance] MvPolynomial.gradedAlgebra

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

attribute [local instance] MvPolynomial.gradedAlgebra

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

open scoped BigOperators

variable (K ι : Type*) [CommRing K]

local notation "P" => MvPolynomial ι K
local notation "G" => ι →₀ ℤ
local notation "A" => AddMonoidAlgebra K G

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

universe uChart

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

universe uTorusChart

theorem closure_specMap_zeroLocus
    {A B : Type uTorusChart} [CommRing A] [CommRing B]
    (f : A →+* B) (q : Ideal B) [q.IsPrime] :
    closure ((Spec.map (CommRingCat.ofHom f)) '' PrimeSpectrum.zeroLocus (q : Set B)) =
      PrimeSpectrum.zeroLocus (q.comap f : Set A) := by
  rw [← PrimeSpectrum.closure_singleton (⟨q, inferInstance⟩ : PrimeSpectrum B)]
  change closure (PrimeSpectrum.comap f '' closure ({⟨q, inferInstance⟩} : Set (PrimeSpectrum B))) = _
  refine (closure_image_closure (PrimeSpectrum.continuous_comap f)).trans ?_
  rw [Set.image_singleton]
  exact PrimeSpectrum.closure_singleton _

theorem affineIntoProj_specMap_point
    {K σ A : Type uTorusChart} [CommRing K] [CommRing A]
    (f : MvPolynomial σ K →+* A) (q : Ideal A) [q.IsPrime] :
    (Spec.map (CommRingCat.ofHom f) ≫ affineIntoProj (k := K) (fun i : σ => X i))
      ⟨q, inferInstance⟩ = coneProjectivePoint (q.comap f) := by
  exact affineIntoProj_polynomial_point (q.comap f)

theorem closure_affineIntoProj_specMap_zeroLocus
    {K σ A : Type uTorusChart} [CommRing K] [CommRing A]
    (f : MvPolynomial σ K →+* A) (q : Ideal A) [q.IsPrime] :
    closure ((Spec.map (CommRingCat.ofHom f) ≫ affineIntoProj (k := K) (fun i : σ => X i)) ''
      PrimeSpectrum.zeroLocus (q : Set A)) =
        ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option σ) K) (coneIdeal (q.comap f)) := by
  rw [← PrimeSpectrum.closure_singleton (⟨q, inferInstance⟩ : PrimeSpectrum A)]
  have hc : Continuous (fun x : PrimeSpectrum A =>
      ((Spec.map (CommRingCat.ofHom f) ≫ affineIntoProj (k := K) (fun i : σ => X i)) x :
        ProjectiveSpectrum (homogeneousSubmodule (Option σ) K))) :=
    (Spec.map (CommRingCat.ofHom f) ≫ affineIntoProj (k := K) (fun i : σ => X i)).continuous
  refine (closure_image_closure hc).trans ?_
  rw [Set.image_singleton]
  exact (congrArg (fun x : ProjectiveSpectrum (homogeneousSubmodule (Option σ) K) =>
    closure ({x} : Set (ProjectiveSpectrum (homogeneousSubmodule (Option σ) K))))
      (affineIntoProj_specMap_point f q)).trans (closure_coneProjectivePoint (q.comap f))

theorem closure_torusLocalization_intoProj_zeroLocus
    {K : Type} [CommRing K]
    (q : Ideal (Localization.Away (∏ i : Fin 4, (X i : MvPolynomial (Fin 4) K)))) [q.IsPrime] :
    let f := algebraMap (MvPolynomial (Fin 4) K)
      (Localization.Away (∏ i : Fin 4, (X i : MvPolynomial (Fin 4) K)))
    closure ((Spec.map (CommRingCat.ofHom f) ≫ affineIntoProj (k := K) (fun i : Fin 4 => X i)) ''
      PrimeSpectrum.zeroLocus (q : Set _)) =
        ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option (Fin 4)) K)
          (coneIdeal (q.comap f)) :=
  closure_affineIntoProj_specMap_zeroLocus _ q

theorem closure_laurentTorus_intoProj_zeroLocus
    {K : Type} [CommRing K]
    (q : Ideal (AddMonoidAlgebra K (Fin 4 →₀ ℤ))) [q.IsPrime] :
    let f := (polynomialToLaurent K (Fin 4)).toRingHom
    closure ((Spec.map (CommRingCat.ofHom f) ≫ affineIntoProj (k := K) (fun i : Fin 4 => X i)) ''
      PrimeSpectrum.zeroLocus (q : Set _)) =
        ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option (Fin 4)) K)
          (coneIdeal (q.comap f)) :=
  closure_affineIntoProj_specMap_zeroLocus _ q

end WeightedTorusJets.Geometry

end

end
end TorusProjectiveClosureSource

end

end SiegelZeros

end OAI
