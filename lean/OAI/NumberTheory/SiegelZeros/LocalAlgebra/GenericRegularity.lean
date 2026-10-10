import Mathlib.LinearAlgebra.Dual.Lemmas
import OAI.NumberTheory.SiegelZeros.Intersection.TorusProjectiveClosure

namespace OAI

namespace SiegelZeros

section

noncomputable section
namespace W58

attribute [local instance 2000] Monoid.toMulAction Semiring.toModule

variable (K : Type*) [Field K]

theorem generic_height_le_cotangent_dimension (p : Ideal (TorusRing K)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) ≤
      Module.finrank (IsLocalRing.ResidueField (GenericLocalRing K p))
        (GenericCotangent K p) := by
  have h := ringKrullDim_le_spanFinrank_maximalIdeal (GenericLocalRing K p)
  rw [generic_local_dimension,
    IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace
      (GenericLocalRing K p)] at h
  exact h

theorem generic_height_le_normal_dimension (p : Ideal (TorusRing K)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) ≤
      Module.finrank (IsLocalRing.ResidueField (GenericLocalRing K p))
        (Module.Dual (IsLocalRing.ResidueField (GenericLocalRing K p))
          (GenericCotangent K p)) := by
  rw [Subspace.dual_finrank_eq
    (K := IsLocalRing.ResidueField (GenericLocalRing K p))
    (V := GenericCotangent K p)]
  exact generic_height_le_cotangent_dimension K p

theorem height_two_le_normal_dimension (p : Ideal (TorusRing K)) [p.IsPrime]
    (hp : p.height = 2) :
    2 ≤ Module.finrank (IsLocalRing.ResidueField (GenericLocalRing K p))
      (Module.Dual (IsLocalRing.ResidueField (GenericLocalRing K p))
        (GenericCotangent K p)) := by
  have h := generic_height_le_normal_dimension K p
  rw [hp] at h
  exact_mod_cast h

theorem height_three_le_normal_dimension (p : Ideal (TorusRing K)) [p.IsPrime]
    (hp : p.height = 3) :
    3 ≤ Module.finrank (IsLocalRing.ResidueField (GenericLocalRing K p))
      (Module.Dual (IsLocalRing.ResidueField (GenericLocalRing K p))
        (GenericCotangent K p)) := by
  have h := generic_height_le_normal_dimension K p
  rw [hp] at h
  exact_mod_cast h

end W58

end

end

end SiegelZeros

end OAI
