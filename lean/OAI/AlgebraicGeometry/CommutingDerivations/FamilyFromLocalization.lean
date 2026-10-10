import OAI.AlgebraicGeometry.CommutingDerivations.DenominatorDescent
import OAI.AlgebraicGeometry.CommutingDerivations.DescentFamily
import OAI.AlgebraicGeometry.CommutingDerivations.LocalizedPartials

namespace OAI

/-!
Construction of a commuting, locally nilpotent, linearly independent family
from a relative localization equivalence and a coefficient-intersection identity.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {K B L σ τ : Type*} [CommRing K] [CommRing B] [CommRing L]
  [Algebra K B] [Algebra K L] [Algebra (MvPolynomial σ K) L]
  [IsScalarTower K (MvPolynomial σ K) L] [Fintype σ] [Fintype τ]
  [IsDomain B] [CharZero B]

theorem exists_commuting_family_of_localization
    (c : MvPolynomial σ K) [IsLocalization.Away c L]
    (hinj : Function.Injective (algebraMap (MvPolynomial σ K) L))
    (e : L ≃ₐ[K] MvPolynomial τ B) (b : B)
    (hec : e (algebraMap (MvPolynomial σ K) L c) = C b)
    (S : Subalgebra K (MvPolynomial σ K))
    (hintersection : ∀ p : MvPolynomial σ K,
      (∃ b : B, e (algebraMap (MvPolynomial σ K) L p) = C b) ↔ p ∈ S) :
    ∃ (N : ℕ) (d : τ → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)),
      (∀ i p, algebraMap (MvPolynomial σ K) L (d i p) =
        (algebraMap (MvPolynomial σ K) L c)^N *
          localizedPartial e i (algebraMap (MvPolynomial σ K) L p)) ∧
      (∀ i, d i c = 0) ∧
      (∀ i j p, d i (d j p) = d j (d i p)) ∧
      (∀ i, LocallyNilpotent (d i)) ∧
      LinearIndependent (MvPolynomial σ K) d ∧
      (∀ p, (∀ i, d i p = 0) ↔ p ∈ S) := by
  classical
  let ι : MvPolynomial σ K →ₐ[K] L :=
    IsScalarTower.toAlgHom K (MvPolynomial σ K) L
  let D : τ → Derivation K L L := localizedPartial e
  have hfix (i : τ) : D i (ι c) = 0 :=
    localizedPartial_fixes_relative e i (ι c) b hec
  have hu : IsUnit (ι c) := IsLocalization.Away.algebraMap_isUnit c
  obtain ⟨N, d, hd⟩ := exists_common_denominator_descent c hinj D
  have hd' (i : τ) (p : MvPolynomial σ K) :
      ι (d i p) = (ι c)^N * D i (ι p) := hd i p
  refine ⟨N, d, hd, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact descended_fixes_parameter ι hinj c N (D i) (d i) (hd' i) (hfix i)
  · intro i j p
    exact descended_commute ι hinj c N (D i) (D j) (d i) (d j)
      (hd' i) (hd' j) (hfix i) (hfix j) (localizedPartials_commute e i j) p
  · intro i
    exact descended_locallyNilpotent ι hinj c N (D i) (d i) (hd' i) (hfix i)
      (localizedPartial_locallyNilpotent e i)
  · apply descended_linearIndependent ι hinj c hu N D d hd' hfix
      (fun j => e.symm (X j)) (localizedPartial_coordinate e)
    intro j
    exact IsLocalization.Away.surj c (e.symm (X j))
  · intro p
    calc
      (∀ i, d i p = 0) ↔ ∀ i, D i (ι p) = 0 :=
        forall_congr' (fun i => descended_kernel ι hinj c hu N (D i) (d i) (hd' i) p)
      _ ↔ ∃ b : B, e (ι p) = C b := localizedPartials_common_kernel e (ι p)
      _ ↔ p ∈ S := hintersection p

end AbhyankarSathaye.CommutingDerivations

end

end OAI
