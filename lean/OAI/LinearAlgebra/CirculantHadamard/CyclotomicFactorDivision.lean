import OAI.LinearAlgebra.CirculantHadamard.CyclotomicProjection
import OAI.LinearAlgebra.CirculantHadamard.LocalDVR

namespace OAI

universe uA

/-!
# A projected factor is integrally divisible by the residue prime

The primitive-character values live in the actual cyclotomic quotient. Their
product is evaluated from the actual group-ring product. The DVR inequality
chooses a factor, and the monic remainder theorem transfers its divisibility
to the smaller cyclic group ring.
-/

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing Polynomial IsDiscreteValuationRing

variable {A : Type uA} [CommRing A]

/-- The ramified DVR and its value of `p` imply the concrete choice of a
divisible projected factor. These are local-ring properties, independent of
the input factors. The scalar and group exponents are both `e + 2`. -/
theorem projected_factor_divisible {p e D : ℕ} [NeZero p] (hp : p.Prime)
    [IsDomain (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))]
    [IsDiscreteValuationRing (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))]
    (hpS : (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) ≠ 0)
    (hD : 0 < D)
    (hpval : addVal (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))
      (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) = (D : ℕ∞))
    (b : Aˣ) (F K : Elem A (p ^ (e + 2)))
    (hFK : F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A))) :
    (∃ F', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
      scalar (p ^ (e + 1)) (p : A) * F') ∨
    (∃ K', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) K =
      scalar (p ^ (e + 1)) (p : A) * K') := by
  let v := cyclicCyclotomicEvaluation A (p ^ (e + 2))
  have hscalar : ∀ a : A, v (scalar (p ^ (e + 2)) a) =
      algebraMap A (AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) a := by
    intro a
    exact v.commutes a
  have hv : v F * v K =
      (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) ^ (e + 2) *
        algebraMap A (AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) (b : A) := by
    have h := congrArg v hFK
    simpa only [map_mul, hscalar, map_pow, map_natCast] using h
  have hb : IsUnit (algebraMap A (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))
      (b : A)) := b.isUnit.map _
  have hchoose := LocalDVR.dvd_or_dvd_of_mul_eq_pow_mul_unit
    hpS hD hpval (Nat.le_add_left 2 e) hb hv
  rcases hchoose with hF | hK
  · left
    simpa only [scalar_natCast] using
      cyclicProjection_divisible_of_cyclotomicEvaluation (e := e + 1) hp F hF
  · right
    simpa only [scalar_natCast] using
      cyclicProjection_divisible_of_cyclotomicEvaluation (e := e + 1) hp K hK

end CirculantHadamard.LocalComparison

end

end OAI
