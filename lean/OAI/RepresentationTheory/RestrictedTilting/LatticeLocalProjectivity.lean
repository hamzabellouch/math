import OAI.RepresentationTheory.RestrictedTilting.BaseChangeProjective
import OAI.RepresentationTheory.RestrictedTilting.LatticeSwap

namespace OAI

namespace FiberFunctorProof
open scoped TensorProduct
variable {R K S ι : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Fintype ι]
  [CommRing S] [Algebra R S]

 

theorem gluedLattice_projective_baseChange (x y : R) (hx : x ≠ 0)
    (hxy : IsRelPrime x y) (P : (ι → K) ≃ₗ[K] (ι → K)) (d e : ℕ)
    (hP : ∀ v ∈ coordinateLattice (R := R), (x*y)^d • P v ∈ coordinateLattice (R := R))
    (hQ : ∀ v ∈ coordinateLattice (R := R), (x*y)^e • P.symm v ∈ coordinateLattice (R := R))
    (hu : IsUnit (algebraMap R S x)) :
    Module.Projective S (S ⊗[R] gluedLattice x y P) := by
  apply projective_baseChange_of_split_smul
    (latticeNumerator x y hx hxy P d hP) (latticeDenominator x y P e hQ) (x^(d+e))
  · ext v : 1
    exact latticeDenominator_numerator x y hx hxy P d e hP hQ v
  · simpa only [map_pow] using hu.pow (d+e)

end FiberFunctorProof

end OAI
